---@diagnostic disable: lowercase-global, undefined-global
-- Sector Times HUD
-- Manual sector counts + PB snapshot per lap + reference toggle

-- ===== Settings (persisted) =====
local json = require('json')

local defaults = {
  useSessionPB    = true,
  showDebugGates  = false,
  showBackground  = true,
  countInvalids   = true,   -- include invalid sectors/laps in PBs?
  refBestSectors  = false,   -- false: fastest complete lap; true: best individual sectors (theoretical)
  auto_placement_interval = 1.0, -- ADD THIS LINE (default to 1 second)
  
}
local settings = ac.storage(defaults)
local SAVE_FOLDER = "savedtimes/"

local gate_editor_active = false -- a flag to know when to draw gates on a map (future use)
local current_route = { name = "", gates = {} }
local GATE_WIDTH = 30.0 -- Default gate width in meters
local gate_debounce_timer = 0.0


-- NEW: State for automatic gate placement
local auto_placement_active = false
local auto_placement_timer = 0.0



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
  return { track="", lap=nil, lapInv=false, secs={}, inv={}, pbNew={} }
end
local current = newLapState()
local last    = newLapState()
local feed

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

-- A constant to control how much smoothing is applied to the delta rate bar.
-- Smaller value = more smoothing, but less responsive.
-- Larger value = less smoothing, but more responsive/jumpy.
local SMOOTHING_FACTOR = 0.45

-- Higher value = faster, more responsive bar animation.
-- Lower value = slower, more dampened bar animation.
local VISUAL_SMOOTHING_SPEED = 10


-- ===== Live delta header state (for big number at the top) =====
local live_delta_value = nil   -- number (e.g., -0.25) ((NOT USED ANYMORE))
local live_delta_color = nil   -- rgbm (green/yellow) chosen in gate logic ((NOT USED ANYMORE))

-- Session references

local bestSecs, bestLap = {}, {}
local sessionBestSecs, sessionBestLap = {}, {}

-- Snapshot used for CURRENT LAP deltas & PB brackets (frozen on lap start, refreshed after lap completion)
-- activePB = { secs={...}, lap=<time>, theoretical=<bool> }
local activePB = { secs={}, lap=nil, theoretical=false }
local lastRefToggle = settings.refBestSectors

local _saved_pbs_loaded = false
local _initial_pbs_loaded = false

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
  return ac.getFolder(ac.FolderID.ACApps) .. '/lua/sector_times_app/' .. rel
end

local SAVE_INDEX_FILE = 'saved_laps_index.json'  -- index kept in app root for simplicity
--local saveIndex = { items = {}, schema = 1 }

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

  -- Write snapshot file
  io.save(appPath("savedlap_" .. id .. ".json"), json.encode(payload))

  -- Update index
  table.insert(saveIndex.items, {
    id = id,
    loopKey = loopKey,
    loopName = loopName,
    carKey = carKey,
    carLabel = carLabel,
    gateCount = payload.gateCount,
    lapMS = payload.lapMS,
    created = created
  })
  saveSaveIndex()

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
  
  -- 1. Determine which subfolder to load from
  local trafficType = getServerTrafficType()
  ac.log(string.format("[Saves] Scanning for PBs for car: %s (%s) | Server Type: %s", carLabel, carKey, trafficType))

  -- 2. Define the specific directory to scan
  local specificSaveDir = appPath(SAVE_FOLDER .. trafficType .. "/")

  if not io.dirExists(specificSaveDir) then
    ac.log("[Saves] Save folder for this traffic type does not exist yet. Nothing to load.")
    return false, "No PBs found for this server type."
  end

  -- Use io.scanDir to get our loop keys from the specific traffic folder
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

          -- Load Gate Splits (for delta timing)
          if type(lapData.gateSplits) == 'table' then
            lapData.gateSplits.lapMS = lapData.lapMS
            bestGateSplits[currentLoopKey] = cloneTable(lapData.gateSplits)
          end
          
          -- Load Server Sector Times (for UI display)
          if type(lapData.serverSectors) == 'table' and lapData.lapMS then
            bestLap[currentLoopKey] = {
              lap = lapData.lapMS / 1000,
              secs = cloneTable(lapData.serverSectors)
            }
            for i, secTime in ipairs(lapData.serverSectors) do
              updBestSector(currentLoopKey, i, secTime, false)
            end
          end

          ac.log(string.format("[Saves] Loaded PB for '%s': %s", lapData.loopName, fmtMS(lapData.lapMS)))
          loadedCount = loadedCount + 1
        end
      end
    end
  end

  if loadedCount == 0 then
    return false, "No saved PBs found for this car on this server type."
  end

  -- Refresh the active PB for the current loop, if one was just loaded
  local currentLoopKey = toKey((current_route and current_route.name) or (current and current.track) or "")
  if currentLoopKey ~= "" and bestGateSplits[currentLoopKey] then
    active_gate_pb = bestGateSplits[currentLoopKey]
    ac.log("[Saves] Active PB for current loop '"..currentLoopKey.."' has been refreshed.")
  end
  
  ac.log(string.format("[Saves] Finished loading. Imported %d PBs for '%s'.", loadedCount, carLabel))
  return true
end


function script.init()
  -- This function is called once when the script loads.
  loadSaveIndex()
end

-- ===== Helpers =====
--local function toKey(name) return (name or ""):lower():gsub("%s+"," "):gsub("^%s+",""):gsub("%s+$","") end

local function startNewGateLap(trackName)
  -- Get the current server traffic type
  local trafficType = getServerTrafficType()
  -- Create a user-friendly version for the log message
  local displayType = "Unknown"
  if trafficType == "traffic" then
    displayType = "Traffic"
  elseif trafficType == "notraffic" then
    displayType = "No Traffic"
  end

  -- THE MODIFIED LINE: Include the traffic type in the log message
  ac.log(string.format("Starting new gate lap for: %s [%s]", trackName, displayType))
  
  -- The active gates are now taken from the globally loaded 'current_route'
  active_route_gates = current_route.gates

  -- This is the same logic from the 'feed' function's lap start hook
  local trackKey = toKey(trackName)

  if settings.useSessionPB then
    ac.log("Mode: Session PB. Using session data for live delta.")
    -- Ensure the table exists for this track, but it might be empty (which is correct for the first lap)
    sessionBestGateSplits[trackKey] = sessionBestGateSplits[trackKey] or {}
    active_gate_pb = sessionBestGateSplits[trackKey]
  else
    ac.log("Mode: Saved PB. Using all-time data for live delta.")
    bestGateSplits[trackKey] = bestGateSplits[trackKey] or {}
    active_gate_pb = bestGateSplits[trackKey]
  end

  ac.log("Loaded " .. #active_gate_pb .. " PB gate splits.")

  -- Reset all gate-related states for the new lap
  last_gate_crossed_index = 0
  last_pos = nil 
  manual_lap_timer = 0.0
  gate_debounce_timer = 0.0
  lap_start_to_gate_1_timer = 0.0
  current_run_gate_splits = {}
  
  -- NEW: Reset delta rate of change state
  last_gate_delta_value = nil
  time_at_last_gate = 0.0
  delta_rate_of_change = nil
  smoothed_delta_rate_of_change = nil
  visual_bar_rate = 0.0
  
  -- Set the UI to its initial state
  ui_gate_delta_text = "Current Lap Delta: -.--"
  ui_gate_delta_color = nil

  live_delta_value = nil
  live_delta_color = nil

  -- We still need to set the 'current.track' for the UI to display the name
  current.track = trackName
  -- Clear out old server sector data for the new run
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

local function drawColoredText(txt, col)
  -- This log will tell us the truth. Is the color object valid or nil?
  --ac.log("drawColoredText called. Text: '" .. tostring(txt) .. "'. Color is: " .. tostring(col))

  if col then
    ui.textColored(txt, col)
  else
    ui.text(txt)
  end
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


local function checkGateCrossing(dt)
  -- ===== AUTO-PLACEMENT LOGIC (unchanged) =====
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
  -- ==========================================================

  if lap_start_to_gate_1_timer >= 0 then
    lap_start_to_gate_1_timer = lap_start_to_gate_1_timer + dt
  end

  gate_debounce_timer = math.max(0, gate_debounce_timer - dt)
  if #current_route.gates == 0 then return end

  local owncar = ac.getCar(0)
  if not owncar or not owncar.position then return end
  local current_pos_vec3 = owncar.position
  
  if last_gate_crossed_index > 0 or lap_start_to_gate_1_timer >= 0 then
    manual_lap_timer = manual_lap_timer + dt
  end
  
  if not last_pos then
    last_pos = {x = current_pos_vec3.x, y = current_pos_vec3.y, z = current_pos_vec3.z}
    return
  end
  
  local next_gate_index = last_gate_crossed_index + 1
  if next_gate_index > #current_route.gates then return end
  
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
        -- THIS IS THE CHANGE: The "Correct Side" log message has been removed.
        found_gate_index = i
        break
      else
        ac.log(string.format("[Gate #%d] CROSSED FROM WRONG SIDE. Ignored. (side_last: %.2f, side_current: %.2f)", i, side_last, side_current))
      end
    end
  end
  
  if found_gate_index ~= -1 then
    -- NEW: SKIPPED GATE DETECTION LOGIC
    local expected_gate = last_gate_crossed_index + 1
    if found_gate_index > expected_gate then
      local first_skipped = expected_gate
      local last_skipped = found_gate_index - 1
      if first_skipped == last_skipped then
        ac.log(string.format("[Gate Logic] SKIPPED Gate #%d. Crossed #%d instead.", first_skipped, found_gate_index))
      else
        ac.log(string.format("[Gate Logic] SKIPPED Gates #%d through #%d. Crossed #%d instead.", first_skipped, last_skipped, found_gate_index))
      end
    end
    -- END NEW LOGIC

    gate_debounce_timer = 0.1
    local total_time_ms

    if found_gate_index == 1 then
      ac.log("Gate 1 crossed. Capturing Split Zero.")
      local split_zero_time_ms = lap_start_to_gate_1_timer * 1000
      lap_start_to_gate_1_timer = -1.0
      manual_lap_timer = 0.0
      table.insert(current_run_gate_splits, split_zero_time_ms)
      total_time_ms = split_zero_time_ms
    else
      local split_zero_time_ms = current_run_gate_splits[1] or 0
      total_time_ms = split_zero_time_ms + (manual_lap_timer * 1000)
      table.insert(current_run_gate_splits, total_time_ms)
    end
    
    --ac.log("Gate " .. found_gate_index .. " triggered. Total Time: " .. fmtMS(total_time_ms))
    
    local pb_split_total_time = active_gate_pb and active_gate_pb[found_gate_index] or nil
    if pb_split_total_time then
      local delta = (total_time_ms - pb_split_total_time) / 1000.0
      
      -- ===== MODIFIED: DELTA RATE OF CHANGE CALCULATION WITH SMOOTHING & FIX =====
      local time_at_this_gate = total_time_ms / 1000.0
      
      -- THE FIX: Add a guard to ensure all values are valid numbers before calculating the rate.
      if last_gate_delta_value ~= nil and type(time_at_this_gate) == "number" and type(time_at_last_gate) == "number" then
        local change_in_time = time_at_this_gate - time_at_last_gate
        if change_in_time > 0.01 then -- This line was causing the crash
          local change_in_delta = delta - last_gate_delta_value
          delta_rate_of_change = change_in_delta / change_in_time
          
          -- Apply Exponential Moving Average (EMA) smoothing
          if smoothed_delta_rate_of_change == nil then
            -- On the first calculation, just snap to the raw value
            smoothed_delta_rate_of_change = delta_rate_of_change
          else
            -- For all subsequent calculations, blend the new raw value with the old smoothed value
            smoothed_delta_rate_of_change = (delta_rate_of_change * SMOOTHING_FACTOR) + (smoothed_delta_rate_of_change * (1 - SMOOTHING_FACTOR))
          end
          
          ac.log(string.format("[Delta Rate] Raw: %.3f, Smoothed: %.3f", delta_rate_of_change, smoothed_delta_rate_of_change))
        end
      else
         ac.log("[Delta Rate] First gate with PB data. Storing initial values, no rate calculated yet.")
         delta_rate_of_change = nil
         smoothed_delta_rate_of_change = nil
      end
      
      -- Update state for the next gate crossing
      last_gate_delta_value = delta
      time_at_last_gate = time_at_this_gate
      -- ===============================================
      
      ui_gate_delta_text = string.format("Current Lap Delta: %+.2f", delta)
      if delta < 0 then ui_gate_delta_color = COL_GREEN else ui_gate_delta_color = COL_YELLOW end
      live_delta_value = delta
      live_delta_color = ui_gate_delta_color
    else
      ui_gate_delta_text = "Current Lap Delta: -.--"
      ui_gate_delta_color = nil
      live_delta_value = nil
      live_delta_color = nil
      
      -- MODIFIED: If there is no PB data for this gate, we can't calculate a delta or its rate. Reset all.
      last_gate_delta_value = nil
      time_at_last_gate = 0.0
      delta_rate_of_change = nil
      smoothed_delta_rate_of_change = 0
    end
    
    last_gate_crossed_index = found_gate_index
  else
    if last_gate_crossed_index > 0 then
      local primary_gate_to_check = current_route.gates[next_gate_index]
      local gate_center_x = (primary_gate_to_check.p1.x + primary_gate_to_check.p2.x) / 2
      local gate_center_z = (primary_gate_to_check.p1.z + primary_gate_to_check.p2.z) / 2
      local dist_to_gate = math.sqrt((current_pos_vec3.x - gate_center_x)^2 + (current_pos_vec3.z - gate_center_z)^2)
      
      if dist_to_gate > 200 then
        ac.log("Off route! Distance to next gate is > 200m. Resetting delta.")
        last_gate_crossed_index = 0
        current_run_gate_splits = {}
        ui_gate_delta_text = "Current Lap Delta: -.--"
        ui_gate_delta_color = nil
        live_delta_value = nil
        live_delta_color = nil
        lap_start_to_gate_1_timer = -1.0
        
        -- MODIFIED: Reset delta rate state on off-track
        last_gate_delta_value = nil
        time_at_last_gate = 0.0
        delta_rate_of_change = nil
        smoothed_delta_rate_of_change = 0.0 -- Set to 0 to have the bar smoothly return to center.
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

local function sum(a) local s=0; for i=1,#a do s=s+(a[i] or 0) end; return s end
local function anyTrue(arr, upto) local n=upto or #arr; for i=1,n do if arr[i] then return true end end return false end

-- robust colored text wrapper (handles CSP arg orders)
local function textColoredCompat(txt, col)
  if ui.textColored and col then
    if not pcall(ui.textColored, txt, col) then
      if not pcall(ui.textColored, col, txt) then ui.text(txt) end
    end
  else ui.text(txt) end
end

-- Colors
local COL_RED    = rgbm.new(0.95, 0.55, 0.55, 1.0)  -- invalid labels
local COL_GREEN  = rgbm.new(0.55, 0.95, 0.55, 1.0)  -- PB/ faster
local COL_YELLOW = rgbm.new(0.95, 0.85, 0.40, 1.0)  -- slower than PB

-- pick color for a time by pace vs PB (≤ PB = green, > PB = yellow)
local function paceColor(val, pbVal, pbHighlight)
  if pbHighlight then return COL_GREEN end             -- explicit PB flag (rarely needed now)
  if pbVal and val then
    local d = val - pbVal
    if d <= 0 then return COL_GREEN else return COL_YELLOW end
  end
  return nil
end

-- deltas: green for negative, yellow for positive, neutral for ~0
local function drawDeltaInline(delta)
  if delta == nil then return end
  -- treat tiny deltas as zero to avoid flicker
  if math.abs(delta) < 0.005 then
    if ui.sameLine then ui.sameLine() end
    ui.text(string.format(" (+%.2f)", 0))
    return
  end
  local sign = (delta >= 0) and "+" or ""
  local txt  = string.format(" (%s%.2f)", sign, delta)
  local col  = (delta < 0) and COL_GREEN or COL_YELLOW
  if ui.sameLine then ui.sameLine() end
  textColoredCompat(txt, col)
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

  -- Determine which data source to use based on the toggle
  local sourceBestLap
  if settings.useSessionPB then
    sourceBestLap = sessionBestLap[key]
  else
    sourceBestLap = bestLap[key]
  end

  -- We are no longer using the "theoretical best" logic for simplicity with this new system.
  -- The reference is always the fastest complete lap from the chosen source.

  if sourceBestLap and sourceBestLap.secs then
    for i, v in ipairs(sourceBestLap.secs) do
      activePB.secs[i] = v
    end
    activePB.lap = sourceBestLap.lap
    activePB.theoretical = false -- It's always a real lap now
  else
    -- If there's no reference from the chosen source, the UI will be blank.
    -- This is the correct behavior (e.g., Session PB mode at the start of a session).
  end
end

-- ===== Parser (fed by chat hook) =====
local function feed(msg)
  if not msg or msg=="" then return end

  -- Started timing of <track>
  local trk = msg:match("^Started%s+timing%s+of%s+(.+)$")
  if trk then

    if auto_placement_active then
      ac.log("Ignoring lap start trigger while auto-placement is active.")
      return
    end
    -- ===== AUTOMATIC ROUTE LOADING LOGIC =====
    local app_folder = ac.getFolder(ac.FolderID.ACApps) .. '/lua/sector_times_app/'
    local filepath = app_folder .. 'routes/' .. trk .. '.json'
    local route_json_string = io.load(filepath)
    
    if route_json_string then
      ac.log("Found matching route file for '" .. trk .. "'. Loading gates.")
      -- Load the route data into our 'current_route' editor variable
      -- This ensures that if the user opens the editor, the active route is shown
      current_route = json.decode(route_json_string)
    else
      ac.log("No matching route file found for '" .. trk .. "'. Gate delta system will be inactive.")
      -- If no file is found, clear out any previously loaded route and set gates to empty
      current_route = { name = trk, gates = {} }
    end
    -- ==========================================

    -- We now trigger our gate lap start logic using the loaded route's name
    startNewGateLap(current_route.name)
    
    -- We also still need to handle the legacy server sector part of the app
    if (current.lap or #current.secs>0) then last = cloneLap(current) end
    current = newLapState(); current.track = trk
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
      local updated = updBestSector(toKey(current.track), idx, secT, inval)
      if updated then current.pbNew[idx] = true end
      return
    end
  end

  -- Lap time for <anything>: M:SS.xx
  do
    local m,s = msg:match("Lap%s+time%s+for%s+.-:%s*(%d+):([%d%.]+)")
    if m then
      local lapInvalidFromServer = msg:find("%(invalid%)") ~= nil
      local lapT  = (tonumber(m) or 0)*60 + (tonumber(s) or 0)
      current.lap, current.lapInv = lapT, lapInvalidFromServer
      local target = sectorCountFor(current.track)
      -- [ logic for calculating final sector, etc. ]
      if #current.secs < target and #current.secs >= 1 then
        local computed = math.max(0, lapT - sum(current.secs))
        local finalInv = anyTrue(current.inv, target-1) or lapInvalidFromServer
        current.secs[target] = computed
        current.inv[target]  = finalInv
        updBestSector(toKey(current.track), target, computed, finalInv)
      elseif #current.secs == target then
        current.inv[target] = (current.inv[target] or false) or anyTrue(current.inv, target-1) or lapInvalidFromServer
      else
        for i=target+1,#current.secs do current.secs[i]=nil; current.inv[i]=nil; current.pbNew[i]=nil end
      end

      -- === NEW LOGIC: ALWAYS UPDATE SESSION PB ===
      last = cloneLap(current)
      if #last.secs == target then
        local trackKey = toKey(last.track)
        local sbl = sessionBestLap[trackKey]
        
        -- THE FIX IS HERE: Re-introduce the 'countInvalids' check
        local shouldUpdate = (not last.lapInv or settings.countInvalids)
        
        if shouldUpdate and (not sbl or last.lap < sbl.lap) then
           ac.log("New session best lap (server sectors).")
           sessionBestLap[trackKey] = { lap=last.lap, secs=cloneTable(last.secs) }
        end
      end
      
      -- ===== AUTOSAVE & DELTA LOGIC (FINAL, CORRECTED VALIDITY) =====
      if #active_route_gates > 0 then
        local trackKey = toKey(last.track)
        local official_lap_ms = last.lap * 1000
        
        -- Create a final, complete set of splits for this lap, finalized with the server's time.
        local completed_splits = cloneTable(current_run_gate_splits)
        completed_splits[#active_route_gates] = official_lap_ms

        -- NEW: Separate validity checks for Session and All-Time PBs
        local isLapValidForSessionPB = (not last.lapInv or settings.countInvalids)
        local isLapValidForAllTimePB = not last.lapInv -- This check is strict and ignores the setting.

        -- === Part 1: Update Session PB ===
        if isLapValidForSessionPB then
          local current_session_pb_ms = (sessionBestGateSplits[trackKey] and sessionBestGateSplits[trackKey][#active_route_gates]) or nil
          if not current_session_pb_ms or official_lap_ms < current_session_pb_ms then
            ac.log("New Session Best for '" .. last.track .. "'. (Lap validity: " .. tostring(not last.lapInv) .. ", Setting allows invalid: " .. tostring(settings.countInvalids) .. ")")
            sessionBestGateSplits[trackKey] = completed_splits
          end
        else
            ac.log("Lap is invalid and setting is off. Skipping Session PB check.")
        end
        
        -- === Part 2: Update All-Time PB & Save to Disk (Strict Check) ===
        if isLapValidForAllTimePB then
          local current_all_time_pb_ms = (bestGateSplits[trackKey] and bestGateSplits[trackKey][#active_route_gates]) or nil
          if not current_all_time_pb_ms or official_lap_ms < current_all_time_pb_ms then
            ac.log("New All-Time Best for '" .. last.track .. "'. Preparing to save.")
            bestGateSplits[trackKey] = completed_splits
            
            -- Save the new All-Time PB to a file. This block is now only reachable by valid laps.
            -- THE FIX IS ON THE NEXT LINE:
            local carKey, carLabel = getCarKeyAndLabel() -- Corrected function name
            local payload = {
              id = tostring(os.time()) .. "_" .. tostring(math.random(1000,9999)),
              schema = 2,
              loopName = last.track,
              loopKey = trackKey,
              carKey = carKey,
              carLabel = carLabel,
              gateCount = #completed_splits,
              gateSplits = completed_splits,
              serverSectors = cloneTable(last.secs),
              lapMS = official_lap_ms,
              created = os.time()
            }
            saveBestLapForPair(payload)
          end
        else
            ac.log("Lap is invalid. Skipping All-Time PB check and disk save.")
        end
      end
      
      -- This part remains the same: reset state for the next lap.
      local trackName = last.track
      current = newLapState()
      current.track = trackName
      snapshotActivePB(trackName)
      
      return
    end
  end
end

-- ===== Chat hook =====
ac.onChatMessage(function(message, senderCarIndex)
  feed(tostring(message or ""))
  return false
end)

-- ===== UI =====
local function labelText(txt, invalidFlag)
  if invalidFlag then
    textColoredCompat(txt, COL_RED)
  else
    ui.text(txt)
  end
end

local function sectorLine(i, val, inv, pbVal, showDelta, showPB)
  -- Label: red if invalid
  labelText(string.format("S%-4d", i) , inv)
  if ui.sameLine then ui.sameLine() end

  -- Time: pace color (green ≤ PB, yellow > PB)
  local tcol = paceColor(val, pbVal, false)
  local ttxt = " " .. fmt(val)
  if tcol then textColoredCompat(ttxt, tcol) else ui.text(ttxt) end

  -- PB bracket (neutral)
  if showPB and pbVal then
    if ui.sameLine then ui.sameLine() end
    ui.text(string.format(" [%s]", fmt(pbVal)))
  end

  -- Delta (green negative, yellow positive, neutral ~0)
  if showDelta and val and pbVal then
    drawDeltaInline(val - pbVal)
  end
end

local function drawLapBlock(title, lap, opts)
  if title ~= "Current Lap" then -- Only draw title for "Last Lap"
    ui.text(title)
  end

  if lap.track and lap.track~="" then ui.text("Route: " .. lap.track) end

  local forCountName = (lap.track and lap.track~="" and lap.track) or (opts.fallbackTrackName or "")
  local target = sectorCountFor(forCountName)

  for i=1,target do
    local v  = lap.secs[i]
    local iv = lap.inv[i]
    -- always fetch PB for coloring, even if we’re not showing [PB] brackets
    local pbForColor = (opts.pbRef and opts.pbRef.secs and opts.pbRef.secs[i]) or nil
    sectorLine(i, v, iv, pbForColor, opts.showDeltas, opts.showSectorPB)
  end

  -- LAP label (red if invalid)
  labelText("LAP:", lap.lapInv)
  if ui.sameLine then ui.sameLine() end

  -- LAP time pace-colored vs PB lap
  local lapPB = opts.pbRef and opts.pbRef.lap or nil
  local lapCol = paceColor(lap.lap, lapPB, false)
  local lapText = " " .. fmt(lap.lap)
  if lapCol then textColoredCompat(lapText, lapCol) else ui.text(lapText) end

  -- Optional [PB]
  if opts.showLapPB and lapPB then
    if ui.sameLine then ui.sameLine() end
    ui.text(string.format(" [%s]", fmt(lapPB)))
    if opts.pbRef and opts.pbRef.theoretical then
      if ui.sameLine then ui.sameLine() end
      ui.text("*")
    end
  end
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

-- NEW RENDER HOOK for drawing in the 3D world
-- This is the correct way to draw objects in the game scene.
render.on('main.root.transparent', function()
  -- This function is called every frame during the 3D rendering phase.
  
  -- We check our setting here. If it's enabled, we call the drawing function.
  if settings.showDebugGates then
    
    -- THE FIX:
    -- 1. Enable depth testing so our gates render behind solid objects.
    render.setDepthMode(render.DepthMode.ReadOnlyLessEqual)

    -- 2. Call our drawing function as before.
    drawDebugGates()

    -- 3. IMPORTANT: Reset the depth mode to default so we don't break other rendering.
    render.setDepthMode(render.DepthMode.Default)

  end
end)

-- HELPER for adding a tooltip to the previous UI item
local function setTooltipOnHover(text)
  if ui.itemHovered() then
    ui.setTooltip(text)
  end
end


local DeltaFont = ui.DWriteFont('Arial', './data')
    :weight(ui.DWriteFont.Weight.Bold)
    :style(ui.DWriteFont.Style.Normal)
    :stretch(ui.DWriteFont.Stretch.Normal)

    

function windowMain(dt)

  -- NEW: LAZY-LOADING FOR SAVED PBs
  -- This runs only ONCE on the first frame the UI is active, guaranteeing
  -- that car and session data is available for the load functions to use.
  if not _initial_pbs_loaded then
    _initial_pbs_loaded = true -- Set flag immediately to prevent re-running
    ac.log("[Saves] UI is active. Performing initial load of PBs for current car...")
    
    local ok, err = loadAllPBsForCar()
    if ok then
      _saved_pbs_loaded = true -- This flag is for the UI button's logic
      ac.log("[Saves] Initial load successful.")
    else
      _saved_pbs_loaded = false
      ac.log("[Saves] Initial load failed or no PBs found: " .. tostring(err))
    end
    
    -- After loading, immediately refresh the active PB for the current track
    -- to ensure the UI updates on this same frame.
    snapshotActivePB(current.track ~= "" and current.track or (last and last.track or ""))
  end

  if settings.showBackground then
    local p1 = vec2(0, 0)
    --local p2 = ui.windowSize()
    local p2 = vec2(300,350)
    local col = ui.styleColor(ui.StyleColor.WindowBg)
    
    local rounding =0.0 
    
    ui.drawRectFilled(p1, p2, col, rounding)
  end

  if settings.showDebugGates then
    drawDebugGates()
  end

  checkGateCrossing(dt)

  -- If reference mode changed, resnapshot immediately
  if lastRefToggle ~= settings.refBestSectors then
    lastRefToggle = settings.refBestSectors
    snapshotActivePB(current.track ~= "" and current.track or last.track or "")
  end

 -- ===== DELTA DISPLAY (WITH ON-DEMAND LOADING) =====

-- 1. Determine the title and tooltip text based on the current mode
local titleText, tooltipText
if settings.useSessionPB then
  titleText = "Lap Delta Mode: Session PB"
  tooltipText = "Reference: Personal Best lap from this session.\nClick to load and switch to All-Time PB."
else
  titleText = "Lap Delta Mode: Saved PB"
  tooltipText = "Reference: All-Time Personal Best (MUST BE VALID).\nClick to switch to Session Best."
end

-- 2. Draw the title and the button on the same line
ui.text(titleText)
ui.sameLine()

-- 3. Create the button with the new on-demand loading logic
if ui.iconButton('toggle_icon.png', vec2(20, 20), nil, nil, 0) then
  -- If we are switching TO Saved PB mode...
  if settings.useSessionPB == true then
    -- ...and we haven't loaded the PBs yet this session...
    if not _saved_pbs_loaded then
      ac.log("[Saves] Loading PBs on-demand from main UI button.")
      local ok, err = loadAllPBsForCar()
      if ok then
        _saved_pbs_loaded = true -- Mark PBs as loaded for this session
      else
        ac.log("[Saves] On-demand load failed: " .. tostring(err))
      end
    end
  end

  -- Flip the setting regardless of whether the load succeeded
  settings.useSessionPB = not settings.useSessionPB
  
  -- Immediately update the UI to reflect the change
  snapshotActivePB(current.track ~= "" and current.track or (last and last.track or ""))
end
setTooltipOnHover(tooltipText)

  -- 4. The rest of the delta display logic remains the same
  DeltaFont = DeltaFont or ui.DWriteFont('Arial', './data')
      :weight(ui.DWriteFont.Weight.Bold)
      :style(ui.DWriteFont.Style.Normal)
      :stretch(ui.DWriteFont.Stretch.Normal)

  -- NEW: VISUAL SMOOTHING CALCULATION
  -- This runs every frame to smoothly animate the bar.
  do
    -- THE FIX: Ensure our target value is never nil before passing it to lerp.
    -- If smoothed_delta_rate_of_change is nil, we treat our target as 0.0.
    local target_rate = smoothed_delta_rate_of_change or 0.0
    
    -- Also ensure the visual_bar_rate itself is not nil, initializing it to 0.0 if necessary.
    visual_bar_rate = visual_bar_rate or 0.0

    -- math.lerp(current, target, factor) moves current towards target
    -- dt * SPEED makes the animation frame-rate independent.
    visual_bar_rate = math.lerp(visual_bar_rate, target_rate, dt * VISUAL_SMOOTHING_SPEED)
  end

  -- MODIFIED: DELTA RATE OF CHANGE VISUALIZER BAR
  do
    -- Configuration for the bar's appearance and behavior
    local BAR_TOTAL_WIDTH = 150
    local BAR_HEIGHT = 8
    local BAR_MAX_RATE = 0.25 
    local BAR_BG_COLOR = rgbm(0.2, 0.2, 0.2, 0.8)

    local bar_start_pos = ui.getCursor()
    
    -- Draw the background container for the bar
    ui.drawRectFilled(bar_start_pos, bar_start_pos + vec2(BAR_TOTAL_WIDTH, BAR_HEIGHT), BAR_BG_COLOR, 2.0)

    -- MODIFIED: Use the visually smoothed value for drawing. No nil check is needed anymore.
    local normalized_rate = math.clamp(visual_bar_rate / BAR_MAX_RATE, -1.0, 1.0)
    
    -- Calculate geometry
    local half_width = BAR_TOTAL_WIDTH / 2
    local center_x = bar_start_pos.x + half_width
    local bar_segment_width = normalized_rate * half_width

    -- Draw the colored segment
    if bar_segment_width > 0.1 then -- Losing time, draw to the right (added threshold to avoid tiny slivers)
      local p1 = vec2(center_x, bar_start_pos.y)
      local p2 = vec2(center_x + bar_segment_width, bar_start_pos.y + BAR_HEIGHT)
      ui.drawRectFilled(p1, p2, COL_YELLOW, 2.0)
    elseif bar_segment_width < -0.1 then -- Gaining time, draw to the left (added threshold)
      local p1 = vec2(center_x + bar_segment_width, bar_start_pos.y)
      local p2 = vec2(center_x, bar_start_pos.y + BAR_HEIGHT)
      ui.drawRectFilled(p1, p2, COL_GREEN, 2.0)
    end
    
    -- Advance the cursor to leave space for the delta number below
    ui.offsetCursorY(BAR_HEIGHT + 4)
  end
  -- END NEW BAR

  -- Draw the delta big and colored
  ui.pushFont(DeltaFont)
  local deltaFontSize = 36

  if live_delta_value ~= nil then
    local delta_text = string.format("%+.2f", live_delta_value)
    local col
    if live_delta_value > 0 then
      col = rgbm(0.88, 0.79, 0.37, 1.0)  -- yellow
    elseif live_delta_value < 0 then
      col = rgbm(0.52, 0.88, 0.52, 1.0)  -- green
    else
      col = rgbm(1.0, 1.0, 1.0, 1.0)  -- white
    end
    ui.dwriteText(delta_text, deltaFontSize, col)
  else
    ui.dwriteText("-.--", deltaFontSize, rgbm(1, 1, 1, 1))
  end
  ui.popFont()

  ui.separator()
  
  -- =======================================================

  -- CURRENT LAP (brackets + deltas)
  
  drawLapBlock("Current Lap", current, {
    showDeltas        = true,
    showSectorPB      = true,
    showLapPB         = true,
    pbRef             = activePB,
    fallbackTrackName = last.track
  })

  -- LAST LAP (always visible; pace-colored times; no brackets/deltas)
  ui.separator()
  drawLapBlock("Last Lap", last, {
    showDeltas        = false,
    showSectorPB      = false,
    showLapPB         = false,
    pbRef             = activePB,
    fallbackTrackName = current.track
  })
end

-- Reset all session data (laps, sectors, PBs)
local function resetAllData()
  bestSecs, bestLap = {}, {}
  current = newLapState()
  last    = newLapState()
  activePB = { secs = {}, lap = nil, theoretical = false }
end

local function drawGateEditor()
  ui.text("Manual Route & Gate Setup")
  ui.separator()

  -- Input for the route name
  local route_name_in_box = ui.inputText("Route Name", current_route.name or "")
  current_route.name = route_name_in_box -- Keep our state in sync with the box

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

  -- The "One-Click" button for adding a gate
  if ui.button("Add Gate at Current Position") then
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
    table.insert(current_route.gates, new_gate)
    ac.log("Gate " .. #current_route.gates .. " created for route '" .. current_route.name .. "'.")
  end

  -- Slider to configure gate width
  GATE_WIDTH = ui.slider("Gate Width", GATE_WIDTH, 10, 80, "%.0f m")
  ui.separator()

  -- UI for managing the route
  ui.text("Manage Route:")
  if ui.button("Save Route") and current_route.name ~= "" then
    -- CORRECTED: Use json.encode to convert the table to a string
    local route_json_string = json.encode(current_route)
    local app_folder = ac.getFolder(ac.FolderID.ACApps) .. '/lua/sector_times_app/'
    io.save(app_folder .. 'routes/' .. current_route.name .. '.json', route_json_string)
    ac.log("Route '" .. current_route.name .. "' saved.")
  end
  
  ui.sameLine()
  if ui.button("Load Route") and route_name_in_box ~= "" then
    local app_folder = ac.getFolder(ac.FolderID.ACApps) .. '/lua/sector_times_app/'
    local route_json_string = io.load(app_folder .. 'routes/' .. route_name_in_box .. '.json')
    if route_json_string then
      -- CORRECTED: Use json.decode to convert the string back to a table
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

-- Separate Settings window (gear button)
function windowSettings(dt)
  -- Helper to avoid nil-table crashes when counting
  local function tlen(t) return (type(t) == "table") and #t or 0 end

  ui.tabBar("SettingsTabs", function()

    -- ===== Main Settings Tab (was "Display") =====
    ui.tabItem("Settings", function() -- Renamed tab from "Display" to "Settings"
      --ui.text("Sector Times Settings")
      --ui.separator()

      if ui.checkbox("Toggle App Background", settings.showBackground) then
    settings.showBackground = not settings.showBackground
  end
  --ui.separator()

      -- Checkbox for counting invalids removed, as per your request
      if ui.checkbox("Count invalid laps towards session PB's", settings.countInvalids) then
        settings.countInvalids = not settings.countInvalids
      end

      ui.separator()
      ui.separator()
      
      --ui.text("Personal Best Management")
      --ui.text()
      
      local cr     = current_route or { name = "", gates = {} }
      local loopName = (cr.name ~= "" and cr.name) or (current and current.track or "") or ""
      local carKey, carLabel = getCarKeyAndLabel()
      
      ui.text("Car:  " .. tostring(carLabel))
      
      ui.text("Loop: " .. (loopName ~= "" and loopName or "— (no route loaded)"))

      --ui.separator()
      
      

      ui.sameLine()
      if ui.button("Delete saved PB for this loop") then
        local loopKey = toKey(loopName)
        if loopKey ~= "" and carKey ~= "" and carKey ~= "unknown_car" then
          -- Get the current server type to build the correct path
          local trafficType = getServerTrafficType()
          local pbFile = appPath(SAVE_FOLDER .. trafficType .. "/" .. loopKey .. "/" .. carKey .. ".json")
          
          if io.fileExists(pbFile) then
            os.remove(pbFile)
            bestGateSplits[loopKey] = nil -- Note: This clears the in-memory PB for the simple key
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
    ui.tabItem("Route Editor", function()
      if ui.checkbox("Show Gates in World (Debug)", settings.showDebugGates) then
    settings.showDebugGates = not settings.showDebugGates
  end
  ui.separator()
      drawGateEditor()
    end)
  end)
end

function windowTitle() return "Sector Times" end

function windowFlags()
  local f = ui.WindowFlags.AlwaysAutoResize  -- keep gear button visible; manifest controls SETTINGS
  
  return f
end