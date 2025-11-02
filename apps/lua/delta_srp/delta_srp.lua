---@diagnostic disable: lowercase-global, undefined-global

-- ===== Settings (persisted) =====
local json = require('json')

local defaults = {
  useSessionPB    = true,
  showDebugGates  = false,
  countInvalids   = true,   -- include invalid sectors/laps in PBs?
  refBestSectors  = false,   -- false: fastest complete lap; true: best individual sectors (theoretical)
  auto_placement_interval = 1.0,
  baseFontSize = 16.0, -- Base font size for the main UI
  bgOpacity = 1.0,
}

-- ===== UI =====

local enable_route_editor = false

local _max_label_width = 0
local _current_item_spacing_y = 4 -- Default fallback value
local _temp_background_on = false

local _car_pbs_for_ui = {} -- Holds the cached list of PBs for the UI
local _car_pbs_ui_loaded = false -- Flag to prevent reloading every frame


local settings = ac.storage(defaults)
local SAVE_FOLDER = "savedtimes/"

local gate_editor_active = false -- a flag to know when to draw gates on a map (future use)
local current_route = { name = "", gates = {} }
local GATE_WIDTH = 30.0 -- Default gate width in meters
local gate_debounce_timer = 0.0

-- ===== NEW: Trigger Gate State & Persistence =====
local trigger_gates = {} -- { ["Route Name"] = { p1 = {x,z}, p2 = {x,z} } }
local TRIGGER_GATES_FILE = "trigger_gates.json"
-- ===============================================

-- ===== NEW: Pre-emptive Timing State =====
local preemptive_timers = {} -- { ["Route Name"] = { startTime = <seconds>, expiryTime = <seconds> } }
local PREEMPTIVE_TIMEOUT = 2.0 -- How long to wait for a server message after a trigger crossing
local trigger_gate_debounce = 0.0

-- ===== NEW: Debug State for Simulating Message Delay =====
local __SIMULATE_MESSAGE_DELAY = false
local MIN_DELAY = 1.0 -- seconds
local MAX_DELAY = 3.0 -- seconds
local pending_message_data = nil -- { message = "...", process_at = <sim_time_in_seconds> }
-- =======================================


-- NEW: State for automatic gate placement
local auto_placement_active = false
local auto_placement_timer = 0.0

local __FORCE_GATE_SKIP_TEST = false



-- ===== Manual sector counts (exact spellings) =====
local manualCount = {
  ["Yaesu Northbound"]    = 2,
  ["Yaesu Southbound"]    = 2,
  ["Shibuya"]             = 2,
  ["Shinjuku"]            = 2,
  ["Bayshore Northbound"] = 4,
  -- all others default to 3
}

local function toKey(s)
  s = tostring(s or "")
  s = s:lower()
  s = s:gsub("[/\\]", "_")       -- slashes → _
  s = s:gsub("%s+", "_")         -- whitespace → _
  s = s:gsub("[^%w_%-]+", "")    -- drop weird chars
  s = s:gsub("_+", "_")          -- collapse multiple _
  s = s:gsub("^_+", ""):gsub("_+$", "") -- trim edges
  return s
end

-- Shallow clone (works for array-like or map-like tables)
if not cloneTable then
  function cloneTable(t)
    local r = {}
    if type(t) == "table" then
      for k, v in pairs(t) do r[k] = v end
    end
    return r
  end
end

local function sectorCountFor(trackName) return manualCount[trackName] or 3 end

-- ===== State =====
local function newLapState()
  return { track="", lap=nil, lapInv=false, secs={}, inv={}, pbNew={}}
end

local current = newLapState()
local last    = newLapState()
local feed

-- NEW: State for the PB notification message
local show_pb_notification = false
local pb_notification_route_name = ""

-- ===== Gate Crossing State =====
local timing_mode = "server"        -- "server" or "gates"
local active_route_gates = {}       -- The gates for the currently active route
local last_gate_crossed_index = 0   -- Which gate we last crossed
local last_pos = nil                -- The car's position on the previous frame
local manual_lap_timer = 0.0
local gate_debounce_timer = 0.0
local lap_start_to_gate_1_timer = -1.0

-- NEW STATE FOR THE DELTA SYSTEM
local bestGateSplits = {}             -- { [trackKey] = {<time1>, <time2>, ...} } Stores the PB gate times for all routes
local sessionBestGateSplits = {}
local active_gate_pb = {}             -- The frozen PB splits for the current lap
local current_run_gate_splits = {}    -- The gate times for the lap currently in progress
local ui_gate_delta_text = "Current Lap Delta: -.--"
local ui_gate_delta_color = nil

-- NEW: STATE FOR DELTA RATE OF CHANGE CALCULATION
local last_gate_delta_value = nil   -- The numerical delta value at the previously crossed gate
local time_at_last_gate = 0.0       -- The total lap time (in seconds) when the last gate was crossed
local delta_rate_of_change = nil    -- The calculated rate of change (delta seconds / real seconds)
local smoothed_delta_rate_of_change = nil -- NEW: The smoothed value for the UI bar.
local visual_bar_rate = 0.0 -- NEW: Smoothed value for the bar's visual animation

-- A constant to control how much smoothing is applied to the delta rate bar.
-- Smaller value = more smoothing, but less responsive.
-- Larger value = less smoothing, but more responsive/jumpy.
local SMOOTHING_FACTOR = 0.45

-- Higher value = faster, more responsive bar animation.
-- Lower value = slower, more dampened bar animation.
local VISUAL_SMOOTHING_SPEED = 10


-- ===== Live delta header state (for big number at the top) =====
local live_delta_value = nil   -- number (e.g., -0.25) 
local live_delta_color = nil   -- rgbm (green/yellow) chosen in gate logic 


-- Session references

local bestSecs, bestLap = {}, {}
local sessionBestSecs, sessionBestLap = {}, {}

-- Snapshot used for CURRENT LAP deltas & PB brackets (frozen on lap start, refreshed after lap completion)
-- activePB = { secs={...}, lap=<time>, theoretical=<bool> }
local activePB = { secs={}, lap=nil, theoretical=false }
local lastRefToggle = settings.useSessionPB
local lastSessionRefToggle = settings.refBestSectors

local _saved_pbs_loaded = false
local _initial_pbs_loaded = false
local _trigger_gates_loaded = false

-- ===== Saving system (per loop + car) =====

local function getServerTrafficType()
  local serverName = ac.getServerName()

  -- If we are offline or the name is empty, treat it as a no-traffic environment.
  if not serverName or serverName == "" then
    return "notraffic" -- Offline practice is always no traffic
  end

  local lowerServerName = serverName:lower()

  -- Search for the keyword "traffic".
  if lowerServerName:find("traffic", 1, true) then
    return "traffic"
  else
    -- If the keyword isn't found, we assume it's a no-traffic server.
    return "notraffic"
  end
end

local function tlen(t) if type(t)=="table" then return #t else return 0 end end


local function appPath(rel)
  return ac.getFolder(ac.FolderID.ACApps) .. '/lua/delta_srp/' .. rel
end

local SAVE_INDEX_FILE = 'saved_laps_index.json'  -- index kept in app root for simplicity
--local saveIndex = { items = {}, schema = 1 } -- This was commented out, keeping it that way.

local function saveTriggerGates()
  local path = appPath(TRIGGER_GATES_FILE)
  io.save(path, json.encode(trigger_gates))
  ac.log("[Triggers] Saved trigger gates to file.")
end

local function loadTriggerGates()
  local path = appPath(TRIGGER_GATES_FILE)
  if io.fileExists(path) then
    local raw = io.load(path)
    if raw then
      local ok, data = pcall(json.decode, raw)
      if ok and type(data) == 'table' then
        trigger_gates = data
        -- A simple helper to count keys in a table
        local count = 0
        for _ in pairs(trigger_gates) do count = count + 1 end
        ac.log("[Triggers] Loaded " .. count .. " trigger gates.")
      else
        ac.log("[Triggers] Failed to decode trigger gates file.")
      end
    end
  else
    ac.log("[Triggers] No trigger gates file found. Starting with an empty set.")
  end
end

-- NEW SAVE FUNCTION: Overwrites the PB file for a specific loop/car pair.
local function saveBestLapForPair(payload)
  if not payload or not payload.loopKey or not payload.carKey then
    ac.log("[Saves] Aborted save: missing loop or car key.")
    return false
  end

  -- 1. Determine the traffic type for the subfolder name
  local trafficType = getServerTrafficType()

  -- 2. Construct the full path including the new traffic subfolder
  local loopDir = appPath(SAVE_FOLDER .. trafficType .. "/" .. payload.loopKey .. "/")
  local savePath = loopDir .. payload.carKey .. ".json"

  ac.log(string.format("[Saves] New PB! Saving lap for '%s' / '%s' (Type: %s)", payload.loopName, payload.carLabel, trafficType))

  -- Ensure the loop's directory exists (io.createDir is recursive)
  if not io.dirExists(loopDir) then
    io.createDir(loopDir)
    ac.log("[Saves] Created new directory: " .. loopDir)
  end

  -- Save the file, overwriting any previous PB.
  io.save(savePath, json.encode(payload))
  ac.log("[Saves] Saved file to: " .. savePath)
  return true
end

local function getCarKeyAndLabel()
  local function try(fn, ...)
    if type(fn) ~= "function" then return nil end
    local ok, v = pcall(fn, ...)
    if ok and v and v ~= "" then return v end
    return nil
  end

  -- Key: prefer a stable identifier
  local key =  try(ac.getCarID, 0)
            or try(ac.getCarModel, 0)   -- model code/id if available
            or try(ac.getCarName, 0)    -- fallback to name
            or "unknown_car"

  -- Label: what we show in UI
  local label =  try(ac.getCarName, 0)
              or key

  return tostring(key), tostring(label)
end

local function fmtMS(ms)
  if not ms then return "-:--.--" end
  return (function(sec) -- reuse your fmt() style but from ms
    local m = math.floor(sec/60); local s = sec - m*60
    return string.format("%d:%05.2f", m, s)
  end)(ms/1000)
end

-- Save the CURRENT gate run as a snapshot file and append to index
local function saveCurrentGateSnapshot()
  if #current_route.gates == 0 then
    ac.log("Save aborted: no route loaded / empty gates.")
    return false, "No route/gates"
  end
  if #current_run_gate_splits == 0 then
    ac.log("Save aborted: no gate splits recorded yet this run.")
    return false, "No splits to save"
  end

  local loopName = current_route.name ~= "" and current_route.name or (current.track or "Unknown Route")
  local loopKey  = toKey(loopName)
  local carKey, carLabel = getCarKeyAndLabel()
  local created = os.time()
  local id = tostring(created) .. "_" .. tostring(math.random(1000,9999))
  local payload = {
    id = id,
    schema = 1,
    appVersion = "0.1",
    loopName = loopName,
    loopKey = loopKey,
    carKey = carKey,
    carLabel = carLabel,
    gateCount = #current_route.gates,
    gateSplits = cloneTable(current_run_gate_splits),
    lapMS = current_run_gate_splits[#current_run_gate_splits] or 0,
    created = created
  }

  -- This seems to refer to a saveIndex that is commented out, so I will comment this out as well.
  -- -- Write snapshot file
  -- io.save(appPath("savedlap_" .. id .. ".json"), json.encode(payload))

  -- -- Update index
  -- table.insert(saveIndex.items, {
  --   id = id,
  --   loopKey = loopKey,
  --   loopName = loopName,
  --   carKey = carKey,
  --   carLabel = carLabel,
  --   gateCount = payload.gateCount,
  --   lapMS = payload.lapMS,
  --   created = created
  -- })
  -- saveSaveIndex()

  ac.log(string.format("Saved snapshot: %s / %s (%s)", loopName, carLabel, fmtMS(payload.lapMS)))
  return true
end

-- NEW FUNCTION to load all PBs for the current car
-- NEW LOAD FUNCTION: Scans the filesystem for all PBs for the current car.
local function loadAllPBsForCar()
  local carKey, carLabel = getCarKeyAndLabel()
  if not carKey or carKey == "unknown_car" then
    return false, "Could not identify the current car."
  end
  
  local trafficType = getServerTrafficType()
  ac.log(string.format("[Saves] Scanning for PBs for car: %s (%s) | Server Type: %s", carLabel, carKey, trafficType))

  local specificSaveDir = appPath(SAVE_FOLDER .. trafficType .. "/")

  if not io.dirExists(specificSaveDir) then
    ac.log("[Saves] Save folder for this traffic type does not exist yet. Nothing to load.")
    return false, "No PBs found for this server type."
  end

  local loopDirs = {}
  io.scanDir(specificSaveDir, '*', function(entryName, attributes)
    if attributes.isDirectory then
      table.insert(loopDirs, entryName)
    end
  end)

  if #loopDirs == 0 then
    ac.log("[Saves] No loop folders found in '"..trafficType.."' directory. Nothing to load.")
    return false, "No saved PBs found for this car on this server type."
  end
  ac.log("[Saves] Found " .. #loopDirs .. " possible loop folders. Checking for saved PBs...")

  local loadedCount = 0
  for _, loopKey in ipairs(loopDirs) do
    local pbFile = specificSaveDir .. loopKey .. "/" .. carKey .. ".json"
    if io.fileExists(pbFile) then
      local raw = io.load(pbFile)
      if raw then
        local ok, lapData = pcall(json.decode, raw)
        if ok and type(lapData) == 'table' then
          local currentLoopKey = lapData.loopKey or loopKey

          -- NEW: Backwards Compatibility and New Format Loading
          local pbGateData = nil
          if type(lapData.gateSplits) == 'table' and type(lapData.lapMS) == 'number' then
            -- This is the NEW structured format. The splits are already physical.
            pbGateData = {
              gateSplits = cloneTable(lapData.gateSplits),
              lapMS = lapData.lapMS
            }
          elseif type(lapData[1]) == 'number' and lapData.schema ~= 2 then
            -- This is the OLD flat array format. The splits are a mix of physical and server time.
            ac.log("[Saves] Old PB format detected for '"..currentLoopKey.."'. Loading as-is for compatibility.")
            local oldSplits = cloneTable(lapData)
            local oldLapMS = oldSplits[#oldSplits]
            pbGateData = {
              gateSplits = oldSplits,
              lapMS = oldLapMS
            }
          end

          if pbGateData then
            bestGateSplits[currentLoopKey] = pbGateData
          end
          
          if type(lapData.serverSectors) == 'table' and lapData.lapMS then
            bestLap[currentLoopKey] = {
              lap = lapData.lapMS / 1000,
              secs = cloneTable(lapData.serverSectors)
            }
            for i, secTime in ipairs(lapData.serverSectors) do
              updBestSector(currentLoopKey, i, secTime, false)
            end
          end

          ac.log(string.format("[Saves] Loaded PB for '%s': %s", lapData.loopName or currentLoopKey, fmtMS(pbGateData and pbGateData.lapMS)))
          loadedCount = loadedCount + 1
        end
      end
    end
  end

  if loadedCount == 0 then
    return false, "No saved PBs found for this car on this server type."
  end
  
  ac.log(string.format("[Saves] Finished loading. Imported %d PBs for '%s'.", loadedCount, carLabel))
  return true
end

-- NEW FUNCTION: Loads and caches all PBs for the current car/server type into a UI-friendly list.
local function loadAndCachePBsForUI()
  -- Reset the cache
  _car_pbs_for_ui = {}
  
  local carKey, carLabel = getCarKeyAndLabel()
  if not carKey or carKey == "unknown_car" then
    ac.log("[UI PBs] Could not identify car to load PBs.")
    return false
  end
  
  local trafficType = getServerTrafficType()
  local specificSaveDir = appPath(SAVE_FOLDER .. trafficType .. "/")

  if not io.dirExists(specificSaveDir) then
    ac.log("[UI PBs] Save directory does not exist. No PBs to show.")
    return false
  end

  ac.log("[UI PBs] Scanning for PBs for UI...")

  local loopDirs = {}
  io.scanDir(specificSaveDir, '*', function(entryName, attributes)
    if attributes.isDirectory then
      table.insert(loopDirs, entryName)
    end
  end)

  if #loopDirs == 0 then return false end

  for _, loopKey in ipairs(loopDirs) do
    local pbFile = specificSaveDir .. loopKey .. "/" .. carKey .. ".json"
    if io.fileExists(pbFile) then
      local raw = io.load(pbFile)
      if raw then
        local ok, lapData = pcall(json.decode, raw)
        if ok and type(lapData) == 'table' and lapData.lapMS and lapData.loopName then
          -- Add the relevant data to our UI list
          table.insert(_car_pbs_for_ui, {
            loopName = lapData.loopName,
            lapMS = lapData.lapMS,
            created = lapData.created, -- Keep this for tooltips
            serverSectors = lapData.serverSectors, -- Store the sector times table
          })
        end
      end
    end
  end

  -- Sort the list alphabetically by route name for consistency
  table.sort(_car_pbs_for_ui, function(a, b)
    return a.loopName < b.loopName
  end)

  ac.log("[UI PBs] Found " .. #_car_pbs_for_ui .. " PBs to display.")
  return #_car_pbs_for_ui > 0
end

function script.init()
  -- This function is called once when the script loads.
  -- loadSaveIndex() -- This was referring to a commented-out variable, commenting out.
end

-- ===== Helpers =====

local function startNewGateLap(trackName, startTimeOffset)
  startTimeOffset = startTimeOffset or 0.0 -- Default to 0 if not provided

  local trafficType = getServerTrafficType()
  local displayType = (trafficType == "traffic" and "Traffic") or (trafficType == "notraffic" and "No Traffic") or "Unknown"

  ac.log(string.format("Starting new official lap for: %s [%s] | Offset: %.3fs", trackName, displayType, startTimeOffset))
  
  active_route_gates = current_route.gates
  local trackKey = toKey(trackName)

  local pb_data_source = nil
  if settings.useSessionPB then
    pb_data_source = sessionBestGateSplits[trackKey]
  else
    pb_data_source = bestGateSplits[trackKey]
  end

  if pb_data_source and type(pb_data_source.gateSplits) == 'table' then
    active_gate_pb = pb_data_source.gateSplits
    --ac.log("Loaded " .. #active_gate_pb .. " PB gate splits for comparison.")
  else
    active_gate_pb = {}
    ac.log("No valid PB data found for this route. Starting fresh.")
  end

  -- Reset all live timing states for the new lap
  last_gate_crossed_index = 0
  manual_lap_timer = startTimeOffset -- Start timer with the calculated offset
  gate_debounce_timer = 0.0
  current_run_gate_splits = {}
  
  last_gate_delta_value = nil
  time_at_last_gate = 0.0
  delta_rate_of_change = nil
  smoothed_delta_rate_of_change = nil
  visual_bar_rate = 0.0
  
  ui_gate_delta_text = "Current Lap Delta: -.--"
  ui_gate_delta_color = nil
  live_delta_value = nil
  live_delta_color = nil

  current.secs = {}
  current.inv = {}
  current.pbNew = {}
  current.lap = nil
  current.lapInv = false
end

local function cloneLap(src)
  local t = newLapState()
  t.track, t.lap, t.lapInv = src.track, src.lap, src.lapInv
  for i,v in ipairs(src.secs)  do t.secs[i]=v end
  for i,v in ipairs(src.inv)   do t.inv[i]=v end
  for i,v in ipairs(src.pbNew) do t.pbNew[i]=v end
  return t
end

-- Checks if two 2D line segments intersect.
-- p1, p2 define the first segment; p3, p4 define the second.
local function lines_intersect(p1, p2, p3, p4)
  -- This check handles cases where one of the points might be nil
  if not p1 or not p2 or not p3 or not p4 then return false end
  local den = (p1.x - p2.x) * (p3.z - p4.z) - (p1.z - p2.z) * (p3.x - p4.x)
  if den == 0 then return false end
  local t = ((p1.x - p3.x) * (p3.z - p4.z) - (p1.z - p3.z) * (p3.x - p4.x)) / den
  local u = -((p1.x - p2.x) * (p1.z - p3.z) - (p1.z - p2.z) * (p1.x - p3.x)) / den
  return t > 0 and t < 1 and u > 0 and u < 1
end

local function drawDebugGates()
  if #current_route.gates == 0 then return end

  local owncar = ac.getCar(0)
  if not owncar or not owncar.position then return end
  
  -- Configuration for the visual gates
  local GATE_HEIGHT = 0.5 -- NEW: Much smaller height for thin strips (in meters)
  local COL_START_FINISH = rgbm(0.2, 0.8, 0.2, 0.6) -- Green (slightly less transparent)
  local COL_NEXT_GATE    = rgbm(0.8, 0.8, 0.2, 0.8) -- Yellow (less transparent)
  local COL_NORMAL_GATE  = rgbm(0.4, 0.6, 1.0, 0.5) -- Blue (less transparent)

  local car_pos = owncar.position
  local next_gate_to_cross = last_gate_crossed_index + 1

  for i, gate in ipairs(current_route.gates) do
    local color = COL_NORMAL_GATE
    if i == 1 then
      color = COL_START_FINISH
    elseif i == next_gate_to_cross then
      color = COL_NEXT_GATE
    end

    -- NEW SIMPLIFIED LOGIC:
    -- Use the car's current Y-position as the base for all gates.
    local ground_y = car_pos.y

    -- Define the 4 corners of the rectangular plane using the new height
    local corner_bl = vec3(gate.p1.x, ground_y, gate.p1.z)       -- Bottom-Left
    local corner_br = vec3(gate.p2.x, ground_y, gate.p2.z)       -- Bottom-Right
    local corner_tr = vec3(gate.p2.x, ground_y + GATE_HEIGHT, gate.p2.z) -- Top-Right
    local corner_tl = vec3(gate.p1.x, ground_y + GATE_HEIGHT, gate.p1.z) -- Top-Left

    -- Draw the quad
    render.quad(corner_bl, corner_br, corner_tr, corner_tl, color)
  end
end

local function cleanupExpiredPreemptiveTimers(dt)
  local currentTime = os.preciseClock() 
  local to_delete = {}
  for routeName, timerData in pairs(preemptive_timers) do
    if currentTime > timerData.expiryTime then
      table.insert(to_delete, routeName)
    end
  end

  if #to_delete > 0 then
    for _, routeName in ipairs(to_delete) do
      preemptive_timers[routeName] = nil
      ac.log("[Triggers] Expired pre-emptive timer for '" .. routeName .. "' removed.")
    end
  end
end

local function resetProvisionalLapState()
  ac.log("[State] Resetting all provisional and live lap state.")
  manual_lap_timer = 0.0
  current_route = { name = "", gates = {} }
  active_route_gates = {}
  last_gate_crossed_index = 0
  current_run_gate_splits = {}
  trigger_gate_debounce = 0.0
  if current then
    current.track = ""
  end
end

local function checkTriggerGateCrossings(dt)
  trigger_gate_debounce = math.max(0, trigger_gate_debounce - dt)
  if trigger_gate_debounce > 0 then return end

  if not last_pos then
    local owncar = ac.getCar(0)
    if owncar and owncar.position then
      local p = owncar.position
      last_pos = { x = p.x, y = p.y, z = p.z }
    end
    return
  end
  
  local owncar = ac.getCar(0)
  if not owncar or not owncar.position then return end
  local current_pos_vec3 = owncar.position
  
  for routeName, gate in pairs(trigger_gates) do
    if not preemptive_timers[routeName] then
      local gate_p1 = gate.p1; local gate_p2 = gate.p2
      
      local gate_vec = {x = gate_p2.x - gate_p1.x, z = gate_p2.z - gate_p1.z}
      local vec_to_last = {x = last_pos.x - gate_p1.x, z = last_pos.z - gate_p1.z}
      local side_last = gate_vec.x * vec_to_last.z - gate_vec.z * vec_to_last.x
      local vec_to_current = {x = current_pos_vec3.x - gate_p1.x, z = current_pos_vec3.z - gate_p1.z}
      local side_current = gate_vec.x * vec_to_current.z - gate_vec.z * vec_to_current.x
      
      if side_last < 0 and side_current >= 0 then
        local gate_center_x = (gate_p1.x + gate_p2.x) / 2
        local gate_center_z = (gate_p1.z + gate_p2.z) / 2
        local dist_sq = (current_pos_vec3.x - gate_center_x)^2 + (current_pos_vec3.z - gate_center_z)^2
        local half_width_sq = (GATE_WIDTH / 2)^2

        if dist_sq <= half_width_sq then
          ac.log("[Triggers] Physical trigger crossed for: '" .. routeName .. "'. Starting pre-emptive timer.")
          local currentTime = os.preciseClock()
          preemptive_timers[routeName] = {
            startTime = currentTime,
            expiryTime = currentTime + PREEMPTIVE_TIMEOUT
          }
          trigger_gate_debounce = 0.5
          break
        end
      end
    end
  end
end


local function checkGateCrossing(dt)
  if auto_placement_active then
    auto_placement_timer = auto_placement_timer + dt
    if auto_placement_timer >= settings.auto_placement_interval then
      auto_placement_timer = 0.0
      local owncar = ac.getCar(0)
      if owncar and owncar.position then
        local car_pos = owncar.position
        local forward_vec2 = vec2(owncar.look.x, owncar.look.z):normalize()
        local side_vec2 = vec2(-forward_vec2.y, forward_vec2.x)
        local new_gate = {
          p1 = { x = car_pos.x - side_vec2.x * (GATE_WIDTH / 2), z = car_pos.z - side_vec2.y * (GATE_WIDTH / 2) },
          p2 = { x = car_pos.x + side_vec2.x * (GATE_WIDTH / 2), z = car_pos.z + side_vec2.y * (GATE_WIDTH / 2) }
        }
        table.insert(current_route.gates, new_gate)
        ac.log("Auto-placed Gate #" .. #current_route.gates)
      end
    end
    return
  end

  gate_debounce_timer = math.max(0, gate_debounce_timer - dt)

  if (current.track and current.track ~= "") or next(preemptive_timers) ~= nil then
    manual_lap_timer = manual_lap_timer + dt
  end
  
  if #current_route.gates == 0 then return end

  local owncar = ac.getCar(0)
  if not owncar or not owncar.position then return end
  local current_pos_vec3 = owncar.position
  
  if not last_pos then
    last_pos = {x = current_pos_vec3.x, y = current_pos_vec3.y, z = current_pos_vec3.z}
    return
  end
  
  local next_gate_index = last_gate_crossed_index + 1
  -- THE PROBLEMATIC LINE HAS BEEN REMOVED FROM HERE
  
  local found_gate_index = -1

  for i = next_gate_index, math.min(next_gate_index + 2, #current_route.gates) do
    local gate_to_check = current_route.gates[i]
    
    local gate_p1 = gate_to_check.p1; local gate_p2 = gate_to_check.p2
    local gate_vec = {x = gate_p2.x - gate_p1.x, z = gate_p2.z - gate_p1.z}
    local vec_to_last = {x = last_pos.x - gate_p1.x, z = last_pos.z - gate_p1.z}
    local side_last = gate_vec.x * vec_to_last.z - gate_vec.z * vec_to_last.x
    local vec_to_current = {x = current_pos_vec3.x - gate_p1.x, z = current_pos_vec3.z - gate_p1.z}
    local side_current = gate_vec.x * vec_to_current.z - gate_vec.z * vec_to_current.x
    
    if (side_last * side_current <= 0) and (gate_debounce_timer == 0) then
      if (side_last < 0 and side_current >= 0) then
        found_gate_index = i
        break
      end
    end
  end

  if __FORCE_GATE_SKIP_TEST and found_gate_index == 5 then
    ac.log("[DEBUG] Intercepted crossing of Gate #5. Forcing a skip to #7.")
    found_gate_index = 7
  end
  
  if found_gate_index ~= -1 then
    gate_debounce_timer = 0.1
    local physical_time_ms = manual_lap_timer * 1000

    local expected_gate_index = last_gate_crossed_index + 1
    if found_gate_index > expected_gate_index then
      ac.log(string.format("[Gate Interpolation] Skipped gates %d through %d. Interpolating times.", expected_gate_index, found_gate_index - 1))
      local start_index = last_gate_crossed_index
      local start_time = (start_index > 0 and current_run_gate_splits[start_index]) or 0
      local end_index = found_gate_index
      local end_time = physical_time_ms
      local time_diff = end_time - start_time
      local index_diff = end_index - start_index

      for i = start_index + 1, end_index - 1 do
        local progress = (i - start_index) / index_diff
        local interpolated_time = start_time + (time_diff * progress)
        table.insert(current_run_gate_splits, interpolated_time)
        ac.log(string.format("  -> Interpolated Gate #%d at %s", i, fmtMS(interpolated_time)))
      end
    end
   
    table.insert(current_run_gate_splits, physical_time_ms)

    local total_time_ms = physical_time_ms
    local pb_split_total_time = active_gate_pb and active_gate_pb[found_gate_index] or nil
    
    if pb_split_total_time then
      local delta = (total_time_ms - pb_split_total_time) / 1000.0
      
      local time_at_this_gate = physical_time_ms / 1000.0
      if last_gate_delta_value ~= nil and type(time_at_this_gate) == "number" and type(time_at_last_gate) == "number" then
        local change_in_time = time_at_this_gate - time_at_last_gate
        if change_in_time > 0.01 then
          local change_in_delta = delta - last_gate_delta_value
          delta_rate_of_change = change_in_delta / change_in_time
          
          if smoothed_delta_rate_of_change == nil then
            smoothed_delta_rate_of_change = delta_rate_of_change
          else
            smoothed_delta_rate_of_change = (delta_rate_of_change * SMOOTHING_FACTOR) + (smoothed_delta_rate_of_change * (1 - SMOOTHING_FACTOR))
          end
        end
      else
         delta_rate_of_change = nil
         smoothed_delta_rate_of_change = nil
      end
      
      last_gate_delta_value = delta
      time_at_last_gate = time_at_this_gate
      
      ui_gate_delta_text = string.format("Current Lap Delta: %+.2f", delta)
      if delta < 0 then ui_gate_delta_color = COL_GREEN else ui_gate_delta_color = COL_YELLOW end
      live_delta_value = delta
      live_delta_color = ui_gate_delta_color
    else
      ui_gate_delta_text = "Current Lap Delta: -.--"
      ui_gate_delta_color = nil
      live_delta_value = nil
      live_delta_color = nil
      
      last_gate_delta_value = nil
      time_at_last_gate = 0.0
      delta_rate_of_change = nil
      smoothed_delta_rate_of_change = 0
    end
    
    last_gate_crossed_index = found_gate_index
  else
    -- =================================================================
    -- NEW: HYBRID off-route detection logic
    -- =================================================================
    if (current.track and current.track ~= "") and #current_route.gates > 0 then
      local target_gate = nil
      local check_mode = "" -- For logging purposes

      if last_gate_crossed_index == 0 then
        -- LAP HAS STARTED, BUT NO GATES CROSSED YET
        -- We are in PREDICTIVE mode: check distance to the NEXT gate (Gate 1).
        target_gate = current_route.gates[1]
        check_mode = "predictive (to Gate 1)"
      else
        -- AT LEAST ONE GATE HAS BEEN CROSSED
        -- We are in NON-PREDICTIVE mode: check distance from the LAST gate.
        target_gate = current_route.gates[last_gate_crossed_index]
        check_mode = "non-predictive (from Gate " .. last_gate_crossed_index .. ")"
      end

      -- If we have a valid target, perform the distance check
      if target_gate then
        local gate_center_x = (target_gate.p1.x + target_gate.p2.x) / 2
        local gate_center_z = (target_gate.p1.z + target_gate.p2.z) / 2
        
        local dist_sq = (current_pos_vec3.x - gate_center_x)^2 + (current_pos_vec3.z - gate_center_z)^2
        
        -- Use squared distance (200*200 = 40000) for efficiency
        if dist_sq > 40000 then
          ac.log(string.format("Off route detected! (%s). Distance > 200m. Resetting lap state.", check_mode))
          
          -- Full state reset
          last_gate_crossed_index = 0
          current_run_gate_splits = {}
          ui_gate_delta_text = "Current Lap Delta: -.--"
          ui_gate_delta_color = nil
          live_delta_value = nil
          live_delta_color = nil
          last_gate_delta_value = nil
          time_at_last_gate = 0.0
          delta_rate_of_change = nil
          smoothed_delta_rate_of_change = 0.0
          preemptive_timers = {}
          current_route = { name = "", gates = {} }
          active_route_gates = {}
          manual_lap_timer = 0.0
          if current then
            current.track = ""
          end
        end
      end
    end
  end
  
  last_pos = {x = current_pos_vec3.x, y = current_pos_vec3.y, z = current_pos_vec3.z}
end

local function fmt(t)
  if not t then return "-:--.--" end
  local m = math.floor(t/60); local s = t - m*60
  return string.format("%d:%05.2f", m, s)
end

local function sum(a)
  if type(a) ~= 'table' then return 0 end
  local s = 0
  for _, v in pairs(a) do
    if type(v) == 'number' then
      s = s + v
    end
  end
  return s
end

local function anyTrue(arr, upto) local n=upto or #arr; for i=1,n do if arr[i] then return true end end return false end

-- Colors
local COL_RED    = rgbm.new(0.95, 0.55, 0.55, 1.0)  -- invalid labels
local COL_GREEN  = rgbm.new(0.55, 0.95, 0.55, 1.0)  -- PB/ faster
local COL_YELLOW = rgbm.new(0.95, 0.85, 0.40, 1.0)  -- slower than PB

-- pick color for a time by pace vs PB (≤ PB = green, > PB = yellow)
local function paceColor(val, pbVal, pbHighlight)
  if pbHighlight then return COL_GREEN end
  if pbVal and val then
    local d = val - pbVal
    if d <= 0 then return COL_GREEN else return COL_YELLOW end
  end
  return nil
end

-- update hidden PBs
function updBestSector(trackK, idx, val, inval)
  if not trackK or trackK=="" or not val then return false end
  if inval and not settings.countInvalids then return false end
  bestSecs[trackK] = bestSecs[trackK] or { secs={} }
  local old = bestSecs[trackK].secs[idx]
  if not old or val < old then
    bestSecs[trackK].secs[idx] = val
    return true
  end
  return false
end

local function updBestLap(trackK, lapT, secsArr, lapInv)
  if not trackK or trackK=="" or not lapT then return end
  if lapInv and not settings.countInvalids then return end
  local bl = bestLap[trackK]
  if not bl or lapT < bl.lap then
    local copy={}; for i,v in ipairs(secsArr) do copy[i]=v end
    bestLap[trackK] = { lap=lapT, secs=copy }
  end
end

-- snapshot PBs for CURRENT LAP use
local function snapshotActivePB(trackName)
  local key = toKey(trackName or "")
  activePB = { secs={}, lap=nil, theoretical=false }
  local targetSectorCount = sectorCountFor(trackName) -- Get the required number of sectors

  if settings.useSessionPB then
    -- SESSION PB MODE
    if settings.refBestSectors then
      -- Theoretical Best Session Sectors
      local sbs = sessionBestSecs[key]
      if sbs and next(sbs) ~= nil then
        local populatedCount = 0
        for k, v in pairs(sbs) do
          activePB.secs[k] = v
          populatedCount = populatedCount + 1
        end

        if populatedCount >= targetSectorCount then
          activePB.lap = sum(sbs)
        else
          activePB.lap = nil
        end
        activePB.theoretical = true
      end
    else
      -- Fastest Complete Session Lap
      local sbl = sessionBestLap[key]
      if sbl and sbl.secs then
        for i, v in ipairs(sbl.secs) do
          activePB.secs[i] = v
        end
        activePB.lap = sbl.lap
        activePB.theoretical = false
      end
    end
  else
    -- ALL-TIME PB MODE (Fastest Complete Lap)
    local bl = bestLap[key]
    if bl and bl.secs then
      for i, v in ipairs(bl.secs) do
        activePB.secs[i] = v
      end
      activePB.lap = bl.lap
      activePB.theoretical = false
    end
  end
end

-- ===== Parser (fed by chat hook) =====
local function feed(msg)
  if not msg or msg=="" then return end

  -- Started timing of <track>
  local trk = msg:match("^Started%s+timing%s+of%s+(.+)$")
  if trk then
    if auto_placement_active then return end

    if current.track and current.track ~= "" then
      ac.log(string.format("Ignoring server start for '%s' because lap for '%s' is already official.", trk, current.track))
      return
    end

    local startTimeOffset = 0.0
    if preemptive_timers[trk] then
      local currentTime = os.preciseClock()
      startTimeOffset = currentTime - preemptive_timers[trk].startTime
      ac.log(string.format("[Triggers] CONFIRMED! Using pre-emptive start for '%s'. Offset: %.3fs", trk, startTimeOffset))
      preemptive_timers = {} -- We have consumed the timer for THIS lap start, so clear the table.
    else
      ac.log("[Triggers] No pre-emptive timer found for '" .. trk .. "'. Starting timer from message (first split may be inaccurate).")
    end

    local app_folder = ac.getFolder(ac.FolderID.ACApps) .. '/lua/delta_srp/'
    local filepath = app_folder .. 'routes/' .. trk .. '.json'
    local route_json_string = io.load(filepath)
    if route_json_string then
      current_route = json.decode(route_json_string)
    else
      current_route = { name = trk, gates = {} }
    end
    
    startNewGateLap(current_route.name, startTimeOffset)
    current.track = trk
    snapshotActivePB(trk)
    return
  end
  
  -- The original server sector parsing logic
  do
    local m,s = msg:match("Sector%s+time:%s*(%d+):([%d%.]+)")
    if m then
      local inval = msg:find("%(invalid%)") ~= nil
      local secT  = (tonumber(m) or 0)*60 + (tonumber(s) or 0)
      local target = sectorCountFor(current.track)
      if #current.secs >= target then
        last = cloneLap(current)
        current = newLapState(); current.track = last.track
      end
      table.insert(current.secs, secT)
      table.insert(current.inv,  inval)
      local idx = #current.secs
      
      if not inval or settings.countInvalids then
        local trackKey = toKey(current.track)
        sessionBestSecs[trackKey] = sessionBestSecs[trackKey] or {}
        if not sessionBestSecs[trackKey][idx] or secT < sessionBestSecs[trackKey][idx] then
          sessionBestSecs[trackKey][idx] = secT
        end
      end

      local updated = updBestSector(toKey(current.track), idx, secT, inval)
      if updated then current.pbNew[idx] = true end

      snapshotActivePB(current.track)

      return
    end
  end

  -- Lap time for <anything>: M:SS.xx
  do
    local m,s = msg:match("Lap%s+time%s+for%s+.-:%s*(%d+):([%d%.]+)")
    if m then
      show_pb_notification = false

      local lapInvalidFromServer = msg:find("%(invalid%)") ~= nil
      local lapT  = (tonumber(m) or 0)*60 + (tonumber(s) or 0)
      current.lap, current.lapInv = lapT, lapInvalidFromServer
      
      local target = sectorCountFor(current.track)
      if #current.secs < target and #current.secs >= 1 then
        local computed = math.max(0, lapT - sum(current.secs))
        local finalInv = anyTrue(current.inv, target-1) or lapInvalidFromServer
        current.secs[target] = computed
        current.inv[target]  = finalInv

        if not finalInv or settings.countInvalids then
          local trackKey = toKey(current.track)
          sessionBestSecs[trackKey] = sessionBestSecs[trackKey] or {}
          if not sessionBestSecs[trackKey][target] or computed < sessionBestSecs[trackKey][target] then
            sessionBestSecs[trackKey][target] = computed
          end
        end

        updBestSector(toKey(current.track), target, computed, finalInv)
      elseif #current.secs == target then
        current.inv[target] = (current.inv[target] or false) or anyTrue(current.inv, target-1) or lapInvalidFromServer
      else
        for i=target+1,#current.secs do current.secs[i]=nil; current.inv[i]=nil; current.pbNew[i]=nil end
      end

      last = cloneLap(current)
      if #last.secs == target then
        local trackKey = toKey(last.track)
        local sbl = sessionBestLap[trackKey]
        
        local shouldUpdate = (not last.lapInv or settings.countInvalids)
        
        if shouldUpdate and (not sbl or last.lap < sbl.lap) then
           ac.log("New session best lap (server sectors).")
           sessionBestLap[trackKey] = { lap=last.lap, secs=cloneTable(last.secs) }
        end
      end
      
      if #active_route_gates > 0 then
        local trackKey = toKey(last.track)
        local official_lap_ms = last.lap * 1000
        
        local completed_lap_data = {
          gateSplits = cloneTable(current_run_gate_splits),
          lapMS = official_lap_ms,
          serverSectors = cloneTable(last.secs)
        }
        
        local isLapValidForSessionPB = (not last.lapInv or settings.countInvalids)
        local isLapValidForAllTimePB = not last.lapInv
        
        if isLapValidForSessionPB then
          local current_session_pb_ms = (sessionBestGateSplits[trackKey] and sessionBestGateSplits[trackKey].lapMS) or nil
          if not current_session_pb_ms or official_lap_ms < current_session_pb_ms then
            ac.log("New Session Best for '" .. last.track .. "'.")
            sessionBestGateSplits[trackKey] = completed_lap_data
          end
        end
        
        if isLapValidForAllTimePB then
          local current_all_time_pb_ms = (bestGateSplits[trackKey] and bestGateSplits[trackKey].lapMS) or nil
          if not current_all_time_pb_ms or official_lap_ms < current_all_time_pb_ms then
            ac.log("New All-Time Best for '" .. last.track .. "'. Preparing to save.")
            bestGateSplits[trackKey] = completed_lap_data
            
            local carKey, carLabel = getCarKeyAndLabel()
            local payload = {
              schema = 2,
              loopName = last.track,
              loopKey = trackKey,
              carKey = carKey,
              carLabel = carLabel,
              gateCount = #completed_lap_data.gateSplits,
              gateSplits = completed_lap_data.gateSplits,
              serverSectors = completed_lap_data.serverSectors,
              lapMS = completed_lap_data.lapMS,
              created = os.time()
            }
            saveBestLapForPair(payload)
            show_pb_notification = true
            pb_notification_route_name = last.track
          end
        end
      end
      
      resetProvisionalLapState()
      
      local lastTrackName = last.track
      snapshotActivePB(lastTrackName)
      
      return
    end
  end
end

-- ===== Chat hook =====
ac.onChatMessage(function(message, senderCarIndex)
  if senderCarIndex == -1 then
    local msg_str = tostring(message or "")

    if __SIMULATE_MESSAGE_DELAY and (msg_str:find("Started timing") or msg_str:find("Lap time") or msg_str:find("Sector time")) then
      local delay = MIN_DELAY + math.random() * (MAX_DELAY - MIN_DELAY)
      local process_at = os.preciseClock() + delay
      
      pending_message_data = { message = msg_str, process_at = process_at }
      
      ac.log(string.format("[DEBUG DELAY] Intercepted/Overwrote server message. Will process in %.2f seconds.", delay))
    else
      feed(msg_str)
    end
  end
  
  return false
end)

-- ===== UI =====

-- NEW: DWrite Font Objects
local DeltaFont = ui.DWriteFont('Segoe UI', '@System')
    :weight(ui.DWriteFont.Weight.Bold)
    :style(ui.DWriteFont.Style.Normal)
    :stretch(ui.DWriteFont.Stretch.Normal)

local MainFont = ui.DWriteFont('Segoe UI', '@System')
    :weight(ui.DWriteFont.Weight.Normal)
    :style(ui.DWriteFont.Style.Normal)
    :stretch(ui.DWriteFont.Stretch.Normal)

local MainFontItalic = ui.DWriteFont('Segoe UI', '@System')
    :weight(ui.DWriteFont.Weight.Normal)
    :style(ui.DWriteFont.Style.Italic)
    :stretch(ui.DWriteFont.Stretch.Normal)

    -- NEW: Variable to hold the calculated vertical item spacing for the current font size
local _current_item_spacing_y = 4 -- Default fallback value


-- NEW: Helper to draw a full line of text and move to the next line.
local function drawDWriteTextLine(text, color)
    color = color or rgbm(1,1,1,1)
    ui.dwriteText(text, settings.baseFontSize, color)
end

-- MODIFIED: Reworked version of sectorLineDWrite for column alignment
local function sectorLineDWrite(i, val, inv, pbVal, showDelta, showPB)
  local startCursorPos = ui.getCursor()
  
  -- Helper to draw a text segment at a specific x,y and return the new x-coordinate
  local function drawSegment(text, color, x_pos)
    color = color or rgbm(1, 1, 1, 1)
    ui.dwriteDrawText(text, settings.baseFontSize, vec2(x_pos, startCursorPos.y), color)
    return x_pos + ui.measureDWriteText(text, settings.baseFontSize).x
  end

  -- Column 1: Draw the Label
  local labelText = string.format("S%d", i)
  ui.dwriteDrawText(labelText, settings.baseFontSize, startCursorPos, inv and COL_RED or nil)

  -- Column 2: Draw the rest of the line, starting from a fixed x-position
  local current_x = startCursorPos.x + _max_label_width

  -- Time: pace color (green ≤ PB, yellow > PB)
  current_x = drawSegment(" " .. fmt(val), paceColor(val, pbVal, false), current_x)

  -- PB bracket (neutral)
  if showPB and pbVal then
    current_x = drawSegment(string.format(" [%s]", fmt(pbVal)), nil, current_x)
  end

  -- Delta (green negative, yellow positive)
  if showDelta and val and pbVal then
    local delta = val - pbVal
    if math.abs(delta) >= 0.005 then
      local sign = (delta >= 0) and "+" or ""
      local deltaText = string.format(" (%s%.2f)", sign, delta)
      local deltaColor = (delta < 0) and COL_GREEN or COL_YELLOW
      current_x = drawSegment(deltaText, deltaColor, current_x)
    end
  end

  -- After drawing the whole line, advance the main UI cursor for the next line.
  local lineHeight = ui.measureDWriteText(" ", settings.baseFontSize).y
  ui.offsetCursorY(lineHeight + _current_item_spacing_y)
end

-- NEW: Reworked version of drawLapBlock using dwrite
local function drawLapBlockDWrite(title, lap, opts)
  if title == "Last Lap" then
    if show_pb_notification then
      local notification_text = string.format("PB for %s saved", pb_notification_route_name)
      drawDWriteTextLine(notification_text, COL_GREEN)
    else
      drawDWriteTextLine("Last Lap")
    end
  elseif title == "Current Lap" then
      -- Don't draw "Current Lap" title to save space
  else
      drawDWriteTextLine(title)
  end

  local forCountName = (lap.track and lap.track ~= "" and lap.track) or (opts.fallbackTrackName or "")
  local target = sectorCountFor(forCountName)

  for i=1,target do
    local v  = lap.secs[i]
    local iv = lap.inv[i]
    local pbForColor = (opts.pbRef and opts.pbRef.secs and opts.pbRef.secs[i]) or nil
    sectorLineDWrite(i, v, iv, pbForColor, opts.showDeltas, opts.showSectorPB)
  end

  -- LAP line using the same direct drawing and alignment method
  local startCursorPos = ui.getCursor()
  local function drawSegment(text, color, x_pos)
    color = color or rgbm(1, 1, 1, 1)
    ui.dwriteDrawText(text, settings.baseFontSize, vec2(x_pos, startCursorPos.y), color)
    return x_pos + ui.measureDWriteText(text, settings.baseFontSize).x
  end
  
  -- Column 1: LAP label (red if invalid)
  ui.dwriteDrawText("LAP:", settings.baseFontSize, startCursorPos, lap.lapInv and COL_RED or nil)
  
  -- Column 2: The rest of the line
  local current_x = startCursorPos.x + _max_label_width
  
  -- LAP time pace-colored vs PB lap
  local lapPB = opts.pbRef and opts.pbRef.lap or nil
  current_x = drawSegment(" " .. fmt(lap.lap), paceColor(lap.lap, lapPB, false), current_x)

  -- Optional [PB]
  if opts.showLapPB and lapPB then
    current_x = drawSegment(string.format(" [%s]", fmt(lapPB)), nil, current_x)
    if opts.pbRef and opts.pbRef.theoretical then
      current_x = drawSegment("*", nil, current_x)
    end
  end

  -- NEW: Add delta calculation and drawing for the total lap time
  if opts.showDeltas and lap.lap and lapPB then
    local delta = lap.lap - lapPB
    if math.abs(delta) >= 0.005 then
      local sign = (delta >= 0) and "+" or ""
      local deltaText = string.format(" (%s%.2f)", sign, delta)
      local deltaColor = (delta < 0) and COL_GREEN or COL_YELLOW
      current_x = drawSegment(deltaText, deltaColor, current_x)
    end
  end

  -- Final newline after the LAP line
  local lineHeight = ui.measureDWriteText(" ", settings.baseFontSize).y
  ui.offsetCursorY(lineHeight + _current_item_spacing_y)
end

render.on('main.root.transparent', function()
  if settings.showDebugGates then
    render.setDepthMode(render.DepthMode.ReadOnlyLessEqual)
    drawDebugGates()
    render.setDepthMode(render.DepthMode.Default)
  end
end)

local function setTooltipOnHover(text)
  if ui.itemHovered() then
    ui.setTooltip(text)
  end
end

-- NEW: Function to calculate layout dimensions based on current font size
local function calculateLayoutMetrics()
    local labels = {"S1", "S2", "S3", "S4", "LAP:"} -- S4 for tracks like Bayshore
    local maxWidth = 0
    for _, label in ipairs(labels) do
        local width = ui.measureDWriteText(label, settings.baseFontSize).x
        if width > maxWidth then
            maxWidth = width
        end
    end
    -- Add a small padding for the space between the label and the time
    _max_label_width = maxWidth + 5 

    -- Calculate vertical item spacing
    local oneLineHeight = ui.measureDWriteText("A", settings.baseFontSize).y
    local twoLineHeight = ui.measureDWriteText("A\nA", settings.baseFontSize).y
    _current_item_spacing_y = twoLineHeight - (oneLineHeight * 2)
end

local function openPBRootForServerType()
  local trafficType = getServerTrafficType()            -- "traffic" | "notraffic"
  local dir = appPath(SAVE_FOLDER .. trafficType .. "/")-- …/apps/lua/delta_srp/savedtimes/<type>/
  if not io.dirExists(dir) then
    io.createDir(dir)                                   -- create if missing so Explorer opens something real
  end
  os.openInExplorer(dir)                                -- correct API per docs
end

-- MODIFIED: windowMain now calculates metrics once per frame
function windowMain(dt)
  if pending_message_data then
    local current_time = os.preciseClock()
    if current_time >= pending_message_data.process_at then
      ac.log("[DEBUG DELAY] Processing delayed message now.")
      feed(pending_message_data.message)
      pending_message_data = nil
    end
  end

  if not _trigger_gates_loaded then
    _trigger_gates_loaded = true
    ac.log("[Triggers] UI is active. Performing initial load of trigger gates...")
    loadTriggerGates()
  end

  if not _initial_pbs_loaded then
    _initial_pbs_loaded = true
    ac.log("[Saves] UI is active. Performing initial load of PBs for current car...")
    
    local ok, err = loadAllPBsForCar()
    if ok then
      _saved_pbs_loaded = true
      ac.log("[Saves] Initial load successful.")
    else
      _saved_pbs_loaded = false
      ac.log("[Saves] Initial load failed or no PBs found: " .. tostring(err))
    end
    
    snapshotActivePB(current.track ~= "" and current.track or (last and last.track or ""))
  end

  local p1, p2 = vec2(0, 0), ui.windowSize()
  local base = ui.styleColor(ui.StyleColor.WindowBg)
  local a = math.max(0.0, math.min(1.0, settings.bgOpacity or 1.0))
  local col = rgbm(base.r, base.g, base.b, a)  -- build a new color; don’t mutate style color
  ui.drawRectFilled(p1, p2, col, 0.0)
  
  if settings.showDebugGates then
    drawDebugGates()
  end

  cleanupExpiredPreemptiveTimers(dt)
  checkTriggerGateCrossings(dt)
  checkGateCrossing(dt)

  do
    local owncar = ac.getCar(0)
    if owncar and owncar.position then
      local p = owncar.position
      last_pos = { x = p.x, y = p.y, z = p.z }
    end
  end

  if lastRefToggle ~= settings.useSessionPB then
    lastRefToggle = settings.useSessionPB
    snapshotActivePB(current.track ~= "" and current.track or last.track or "")
  end
  
  if lastSessionRefToggle ~= settings.refBestSectors then
    lastSessionRefToggle = settings.refBestSectors
    snapshotActivePB(current.track ~= "" and current.track or last.track or "")
  end
  
  -- MODIFIED: Use the correct font stack for DWrite
  ui.pushDWriteFont(MainFont)

  calculateLayoutMetrics()
  
  -- ===== DELTA DISPLAY (WITH ON-DEMAND LOADING & ITALICS) =====
  do
    local tooltipText
    if settings.useSessionPB then
      tooltipText = "Reference: Personal Best lap from this session.\nClick to load and switch to All-Time PB."
    else
      tooltipText = "Reference: All-Time Personal Best (MUST BE VALID).\nClick to switch to Session Best."
    end
    
    -- Draw text in two parts for italics
    ui.dwriteText("Reference Mode: ", settings.baseFontSize)
    ui.sameLine(0, 5)
    
    -- MODIFIED: Use the correct font stack push for italics
    ui.pushDWriteFont(MainFontItalic)
    local italicPart = settings.useSessionPB and "Session PB" or "Saved PB"
    ui.dwriteText(italicPart, settings.baseFontSize)
    ui.popDWriteFont() -- MODIFIED
    
    ui.sameLine()

    if ui.iconButton('toggle_icon.png##MainModeToggle', vec2(20, 20), nil, nil, 0) then
      if settings.useSessionPB == true then
        if not _saved_pbs_loaded then
          ac.log("[Saves] Loading PBs on-demand from main UI button.")
          local ok, err = loadAllPBsForCar()
          if ok then _saved_pbs_loaded = true
          else ac.log("[Saves] On-demand load failed: " .. tostring(err))
          end
        end
      end
      settings.useSessionPB = not settings.useSessionPB
      snapshotActivePB(current.track ~= "" and current.track or (last and last.track or ""))
    end
    setTooltipOnHover(tooltipText)
  end

  do
    local target_rate = smoothed_delta_rate_of_change or 0.0
    visual_bar_rate = visual_bar_rate or 0.0
    visual_bar_rate = math.lerp(visual_bar_rate, target_rate, dt * VISUAL_SMOOTHING_SPEED)
  end

  do
    local BAR_TOTAL_WIDTH = math.max(100, ui.availableSpaceX())
    local BAR_HEIGHT = 8
    local BAR_MAX_RATE = 0.25 
    local BAR_BG_COLOR = rgbm(0.2, 0.2, 0.2, 0.8)
    local bar_start_pos = ui.getCursor()
    ui.drawRectFilled(bar_start_pos, bar_start_pos + vec2(BAR_TOTAL_WIDTH, BAR_HEIGHT), BAR_BG_COLOR, 2.0)
    local normalized_rate = math.clamp(visual_bar_rate / BAR_MAX_RATE, -1.0, 1.0)
    local half_width = BAR_TOTAL_WIDTH / 2
    local center_x = bar_start_pos.x + half_width
    local bar_segment_width = normalized_rate * half_width
    if bar_segment_width > 0.1 then
      local p1 = vec2(center_x, bar_start_pos.y)
      local p2 = vec2(center_x + bar_segment_width, bar_start_pos.y + BAR_HEIGHT)
      ui.drawRectFilled(p1, p2, COL_YELLOW, 2.0)
    elseif bar_segment_width < -0.1 then
      local p1 = vec2(center_x + bar_segment_width, bar_start_pos.y)
      local p2 = vec2(center_x, bar_start_pos.y + BAR_HEIGHT)
      ui.drawRectFilled(p1, p2, COL_GREEN, 2.0)
    end
    ui.offsetCursorY(BAR_HEIGHT + 4)
  end

  ui.pushDWriteFont(DeltaFont)
  local deltaFontSize = settings.baseFontSize * 2.2
  if live_delta_value ~= nil then
    local delta_text = string.format("%+.2f", live_delta_value)
    local col
    if live_delta_value > 0 then col = rgbm(0.88, 0.79, 0.37, 1.0)
    elseif live_delta_value < 0 then col = rgbm(0.52, 0.88, 0.52, 1.0)
    else col = rgbm(1.0, 1.0, 1.0, 1.0)
    end
    ui.dwriteText(delta_text, deltaFontSize, col)
  else
    ui.dwriteText("-.--", deltaFontSize, rgbm(1, 1, 1, 1))
  end
  ui.popDWriteFont()
  ui.separator()
  
  
  do
    if settings.useSessionPB then
      if ui.iconButton('toggle_icon.png##SessionRefToggle', vec2(20, 20), nil, nil, 0) then
        settings.refBestSectors = not settings.refBestSectors
      end
      if ui.itemHovered() then
        local currentMode = settings.refBestSectors and "Best Sectors*" or "Fastest Lap"
        ui.setTooltip("Current: " .. currentMode .. "\n\nToggles between fastest sectors and sectors from fastest lap.\n\n* indicates a theoretical laptime.")
      end
      ui.sameLine(nil, 5)
    end
    
    ui.dwriteText("Route: ", settings.baseFontSize)
    ui.sameLine(0, 5)

    -- MODIFIED: Use the correct font stack push for italics
    ui.pushDWriteFont(MainFontItalic)
    local routeName = (current.track and current.track ~= "") and current.track
                   or (last.track and last.track ~= "") and last.track
                   or "N/A"
    ui.dwriteText(routeName, settings.baseFontSize)
    ui.popDWriteFont()
  end

  drawLapBlockDWrite("Current Lap", current, {
    showDeltas        = true,
    showSectorPB      = true,
    showLapPB         = true,
    pbRef             = activePB,
    fallbackTrackName = last.track
  })
  ui.separator()
  drawLapBlockDWrite("Last Lap", last, {
    showDeltas        = false,
    showSectorPB      = false,
    showLapPB         = false,
    pbRef             = activePB,
    fallbackTrackName = current.track
  })

  ui.popDWriteFont()
end

local function resetAllData()
  bestSecs, bestLap = {}, {}
  current = newLapState()
  last    = newLapState()
  activePB = { secs = {}, lap = nil, theoretical = false }
end

local function drawGateEditor()
  ui.text("Manual Route & Gate Setup")
  ui.separator()

  local route_name_in_box = ui.inputText("Route Name", current_route.name or "")
  current_route.name = route_name_in_box

  local button_text = auto_placement_active and "Stop Automatic Placement" or "Start Automatic Gate Placement"
  local button_color = auto_placement_active and COL_RED or nil
  
  if ui.button(button_text, nil, button_color) then
    auto_placement_active = not auto_placement_active
    if auto_placement_active then
      ac.log("Automatic gate placement STARTED for route '" .. current_route.name .. "'. Drive to place gates.")
      auto_placement_timer = 1
    else
      ac.log("Automatic gate placement STOPPED.")
    end
  end

  settings.auto_placement_interval = ui.slider("Placement Interval", settings.auto_placement_interval, 0.2, 5.0, "%.1f s")
  ui.separator()
  ui.text("Create Gates:")

  if ui.button("Add Trigger Gate for Current Route") then
    local routeName = current_route.name
    if routeName and routeName ~= "" then
      local owncar = ac.getCar(0)
      local car_pos = owncar.position
      local forward_vec2 = vec2(owncar.look.x, owncar.look.z):normalize()
      local side_vec2 = vec2(-forward_vec2.y, forward_vec2.x)
      local half_width = GATE_WIDTH / 2.0
      local point_a_vec2 = vec2(car_pos.x, car_pos.z) + side_vec2 * half_width
      local point_b_vec2 = vec2(car_pos.x, car_pos.z) - side_vec2 * half_width
      local new_gate = {
        p1 = { x = point_a_vec2.x, z = point_a_vec2.y },
        p2 = { x = point_b_vec2.x, z = point_b_vec2.y }
      }
      trigger_gates[routeName] = new_gate
      ac.log("Trigger gate created/updated for route '" .. routeName .. "'.")
      saveTriggerGates()
    else
      ac.log("Cannot add trigger gate: Route Name is empty.")
    end
  end

  GATE_WIDTH = ui.slider("Gate Width", GATE_WIDTH, 10, 80, "%.0f m")
  ui.separator()

  ui.text("Manage Route:")
  if ui.button("Save Route") and current_route.name ~= "" then
    local route_json_string = json.encode(current_route)
    local app_folder = ac.getFolder(ac.FolderID.ACApps) .. '/lua/delta_srp/'
    io.save(app_folder .. 'routes/' .. current_route.name .. '.json', route_json_string)
    ac.log("Route '" .. current_route.name .. "' saved.")
  end
  
  ui.sameLine()
  if ui.button("Load Route") and route_name_in_box ~= "" then
    local app_folder = ac.getFolder(ac.FolderID.ACApps) .. '/lua/delta_srp/'
    local route_json_string = io.load(app_folder .. 'routes/' .. route_name_in_box .. '.json')
    if route_json_string then
      current_route = json.decode(route_json_string)
      ac.log("Route '" .. current_route.name .. "' loaded.")
    else
      ac.log("Could not find route file for '" .. route_name_in_box .. "'.")
    end
  end

  ui.sameLine()
  if ui.button("New / Clear") then
    current_route = { name = "", gates = {} }
  end
end

function windowSettings(dt)
  local function tlen(t) return (type(t) == "table") and #t or 0 end

  ui.tabBar("SettingsTabs", function()
    ui.tabItem("Settings", function()

      ui.separator()

      if ui.button("Force Reset Lap State") then
    ac.log("[State] Manual state reset triggered by user.")
    resetProvisionalLapState()
    -- Also reset the 'last' lap state to clear the UI completely
    last = newLapState()
end
ui.separator()

if ui.itemHovered() then
    ui.setTooltip("Use this if the app gets stuck and won't start a new lap.")
end

settings.bgOpacity = settings.bgOpacity or 1.0
do
  local ref = refnumber(settings.bgOpacity)
  if ui.slider("##bgOpacity", ref, 0.0, 1.0, "Background Opacity: %.2f") then
    settings.bgOpacity = ref.value
  end
end

      -- Font size slider
      settings.baseFontSize = ui.slider("Font Size", settings.baseFontSize, 12.0, 36.0, "%.0f px")
      
      -- NEW LOGIC: Temporarily show background while dragging the slider
      
      
      setTooltipOnHover("Adjusts the base font size for the main display.\nResize the window after changing.")
      
      if ui.checkbox("Count invalid laps towards session PB's", settings.countInvalids) then
        settings.countInvalids = not settings.countInvalids
      end
      do
        local tooltip_text = "Toggles whether the app can use your best invalid laps/sectors of this session as a reference.\n\nThis setting does not affect all-time Saved PB's which are saved to disk and can be loaded in future sessions, those MUST be valid."
        setTooltipOnHover(tooltip_text)
      end

      ui.separator()
      ui.separator()
      
      local cr     = current_route or { name = "", gates = {} }
      local loopName = (cr.name ~= "" and cr.name) or (current and current.track or "") or ""
      local carKey, carLabel = getCarKeyAndLabel()
      
      ui.text("Car:  " .. tostring(carLabel))
      ui.text("Loop: " .. (loopName ~= "" and loopName or "— (no route loaded)"))

      ui.sameLine()
      if ui.button("Delete saved PB for this loop") then
        local loopKey = toKey(loopName)
        if loopKey ~= "" and carKey ~= "" and carKey ~= "unknown_car" then
          local trafficType = getServerTrafficType()
          local pbFile = appPath(SAVE_FOLDER .. trafficType .. "/" .. loopKey .. "/" .. carKey .. ".json")
          
          if io.fileExists(pbFile) then
            os.remove(pbFile)
            bestGateSplits[loopKey] = nil
            bestLap[loopKey] = nil
            active_gate_pb = {}
            activePB = { secs={}, lap=nil, theoretical=false }
            ac.log("[Saves] Deleted PB file: " .. pbFile)
          else
            ac.log("[Saves] No PB file exists to be deleted for this pair/traffic type.")
          end
        end
      end
    end)

    -- =========================================================================
    -- START: NEW "Saved PBs" TAB
    -- =========================================================================
    ui.tabItem("Saved PBs", function()
      if not _car_pbs_ui_loaded then
        loadAndCachePBsForUI()
        _car_pbs_ui_loaded = true
      end

      local carKey, carLabel = getCarKeyAndLabel()
      local trafficType = getServerTrafficType()
      local displayType = (trafficType == "traffic" and "Traffic") or "No Traffic"

      ui.text("Showing saved PBs for:")
      ui.textDisabled(string.format("Car: %s", carLabel))
      ui.textDisabled(string.format("Server Type: %s", displayType))
      
      ui.sameLine(nil, 20)
      if ui.button("Open Saved Times Folder") then
  openPBRootForServerType()
end
if ui.itemHovered() then
  ui.setTooltip("Opens the savedtimes folder where the .json time files for each route are saved. You can share your time files with others.")
end

      ui.separator()

      
      ui.childWindow("PBListContainer", vec2(-1, 150), true, 0, function()
        if #_car_pbs_for_ui == 0 then
          ui.text("No saved PBs found for this car")
        else
          for i, pbData in ipairs(_car_pbs_for_ui) do
            ui.text(pbData.loopName)
            ui.sameLine(150) 
            ui.textColored(fmtMS(pbData.lapMS), COL_GREEN)

            if ui.itemHovered() then
  local tooltip_lines = {}
  local has_content = false -- A flag to track if we've added any lines yet

  -- Part 1: Build the sector times line
  if pbData.serverSectors and type(pbData.serverSectors) == 'table' and #pbData.serverSectors > 0 then
    local sector_parts = {}
    for i, secTime in ipairs(pbData.serverSectors) do
      table.insert(sector_parts, string.format("S%d: %s", i, fmt(secTime)))
    end
    table.insert(tooltip_lines, table.concat(sector_parts, " | "))
    has_content = true -- We've added the sector line
  end

  -- Part 2: Build the metadata line
  if pbData.created then
    -- THE FIX: If we already have content (the sector line), add a blank line first.
    if has_content then
      table.insert(tooltip_lines, "") -- This creates the empty line.
    end
    
    table.insert(tooltip_lines, "Set on: " .. os.date("%Y-%m-%d %H:%M:%S", pbData.created))
  end
  
  -- Part 3: Combine all lines into a single tooltip string
  if #tooltip_lines > 0 then
    ui.setTooltip(table.concat(tooltip_lines, "\n"))
  end
end
          end
        end
      end)
    end)
    -- =========================================================================
    -- END: NEW "Saved PBs" TAB
    -- =========================================================================


    if enable_route_editor then
      
      ui.tabItem("Route Editor", function()
      ui.textColored("--- DEBUGGING ---", COL_YELLOW)

      if ui.checkbox("Show Gates in World (Debug)", settings.showDebugGates) then
        settings.showDebugGates = not settings.showDebugGates
      end

      if ui.checkbox("Simulate Server Message Delay", __SIMULATE_MESSAGE_DELAY) then
        __SIMULATE_MESSAGE_DELAY = not __SIMULATE_MESSAGE_DELAY
        if not __SIMULATE_MESSAGE_DELAY then
          pending_message_data = nil
        end
      end
      if __SIMULATE_MESSAGE_DELAY then
        ui.indent()
        MIN_DELAY = ui.slider("Min Delay", MIN_DELAY, 0.5, 5.0, "%.1f s")
        MAX_DELAY = ui.slider("Max Delay", MAX_DELAY, 0.5, 5.0, "%.1f s")
        if MIN_DELAY > MAX_DELAY then MAX_DELAY = MIN_DELAY end
        ui.unindent()
      end

      if ui.checkbox("Force Gate Skip (Test)", __FORCE_GATE_SKIP_TEST) then
        __FORCE_GATE_SKIP_TEST = not __FORCE_GATE_SKIP_TEST
        if __FORCE_GATE_SKIP_TEST then
          ac.log("[DEBUG] Gate skip simulation ENABLED. Crossing gate #5 will simulate a skip to #7.")
        else
          ac.log("[DEBUG] Gate skip simulation DISABLED.")
        end
      end

      ui.separator()
      drawGateEditor()
    end)
  end
  end)
end

function windowTitle() return "Sector Times" end

function windowFlags()
  return 0
end