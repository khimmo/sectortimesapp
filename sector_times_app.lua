---@diagnostic disable: lowercase-global, undefined-global
-- Sector Times HUD
-- Manual sector counts + PB snapshot per lap + reference toggle

-- ===== Settings (persisted) =====
local json = require('json')

local defaults = {
  showInvalid     = true,    -- highlight invalid labels in red
  countInvalids   = false,   -- include invalid sectors/laps in PBs?
  refBestSectors  = false,   -- false: fastest complete lap; true: best individual sectors (theoretical)
  auto_placement_interval = 1.0, -- ADD THIS LINE (default to 1 second)
  
}
local settings = ac.storage(defaults)
local SAVE_FOLDER = "savedtimes/"

local gate_editor_active = false -- a flag to know when to draw gates on a map (future use)
local current_route = { name = "", gates = {} }
local GATE_WIDTH = 20.0 -- Default gate width in meters
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

saveIndex = saveIndex or { items = {}, schema = 1 }


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

-- NEW STATE FOR THE DELTA SYSTEM
local bestGateSplits = {}             -- { [trackKey] = {<time1>, <time2>, ...} } Stores the PB gate times for all routes
local active_gate_pb = {}             -- The frozen PB splits for the current lap
local current_run_gate_splits = {}    -- The gate times for the lap currently in progress
local ui_gate_delta_text = "Current Lap Delta: -.--"
local ui_gate_delta_color = nil

-- ===== Live delta header state (for big number at the top) =====
local live_delta_value = nil   -- number (e.g., -0.25) ((NOT USED ANYMORE))
local live_delta_color = nil   -- rgbm (green/yellow) chosen in gate logic ((NOT USED ANYMORE))

-- Session references
-- bestSecs[trackKey].secs[i] = best time for sector i (session)
-- bestLap[trackKey]          = { lap=<time>, secs={...} } fastest complete lap (session)
local bestSecs, bestLap = {}, {}

-- Snapshot used for CURRENT LAP deltas & PB brackets (frozen on lap start, refreshed after lap completion)
-- activePB = { secs={...}, lap=<time>, theoretical=<bool> }
local activePB = { secs={}, lap=nil, theoretical=false }
local lastRefToggle = settings.refBestSectors

-- ===== Saving system (per loop + car) =====

local function tlen(t) if type(t)=="table" then return #t else return 0 end end


local function appPath(rel)
  return ac.getFolder(ac.FolderID.ACApps) .. '/lua/sector_times_app/' .. rel
end

local SAVE_INDEX_FILE = 'saved_laps_index.json'  -- index kept in app root for simplicity
--local saveIndex = { items = {}, schema = 1 }

local function loadSaveIndex()
  ac.log("[Saves] Loading save index from disk...")
  
  -- Always start with a fresh table to ensure no old data remains
  saveIndex = { items = {}, schema = 1 }

  local index_path = appPath(SAVE_INDEX_FILE)
  local s = io.load(index_path)
  
  if s and s ~= "" then
    local ok, data = pcall(json.decode, s)
    if ok and type(data) == 'table' and type(data.items) == 'table' then
      saveIndex = data
      ac.log("[Saves] Successfully decoded index. Loaded " .. #saveIndex.items .. " items.")
    else
      ac.log("[Saves] ERROR: Failed to decode or parse JSON from index file.")
    end
  else
    ac.log("[Saves] Index file not found or is empty.")
  end
end

local function saveSaveIndex()
  ac.log("[Saves] Attempting to save index with " .. #saveIndex.items .. " items.")
  local encoded_data = json.encode(saveIndex)
  if encoded_data then
    io.save(appPath(SAVE_INDEX_FILE), encoded_data)
    ac.log("[Saves] Index saved successfully.")
  else
     ac.log("[Saves] ERROR: Failed to encode save index to JSON. Nothing was saved.")
  end
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
local function loadAllBestLapsForCar()

  loadSaveIndex()

  local carKey, carLabel = getCarKeyAndLabel()
  if not carKey or carKey == "unknown_car" then
    return false, "Could not identify the current car."
  end
  
  ac.log(string.format("[Saves] Searching for all best laps for car: %s (%s)", carLabel, carKey))

  -- Step 1: Find the single best lap ID for each unique loop for this car
  local bestLapsByLoop = {} -- { [loopKey] = { bestTime = 12345, snapshotID = "...", loopName = "..." } }
  for _, item in ipairs(saveIndex.items or {}) do
    if item.carKey == carKey then
      local loopKey = item.loopKey
      local lapTime = item.lapMS or 999999999 -- Use a huge number for laps with no time
      
      if not bestLapsByLoop[loopKey] or lapTime < bestLapsByLoop[loopKey].bestTime then
        bestLapsByLoop[loopKey] = {
          bestTime = lapTime,
          snapshotID = item.id,
          loopName = item.loopName
        }
      end
    end
  end
  
  -- Step 2: Now load the data from each of those best lap files
  local loadedCount = 0
  for loopKey, data in pairs(bestLapsByLoop) do
    local raw = io.load(appPath("savedlap_" .. data.snapshotID .. ".json"))
    if not raw then
      ac.log(string.format("[Saves] WARNING: Snapshot file missing for loop '%s', ID: %s", data.loopName, data.snapshotID))
    else
      local ok, lapData = pcall(json.decode, raw)
      if ok and type(lapData) == 'table' and type(lapData.gateSplits) == 'table' then
        -- This is where we populate the session's PB data
        bestGateSplits[loopKey] = cloneTable(lapData.gateSplits)
        ac.log(string.format("[Saves] Loaded PB for '%s': %s", data.loopName, fmtMS(lapData.lapMS)))
        loadedCount = loadedCount + 1
      else
        ac.log(string.format("[Saves] WARNING: Corrupt snapshot file for loop '%s', ID: %s", data.loopName, data.snapshotID))
      end
    end
  end

  if loadedCount == 0 then
    return false, "No saved snapshots found for this car."
  end

  -- Step 3: Refresh the active PB for the current loop, if it was just loaded
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
  ac.log("Starting new gate lap for: " .. trackName)
  
  -- The active gates are now taken from the globally loaded 'current_route'
  active_route_gates = current_route.gates

  -- This is the same logic from the 'feed' function's lap start hook
  local trackKey = toKey(trackName)
  bestGateSplits[trackKey] = bestGateSplits[trackKey] or {}
  active_gate_pb = bestGateSplits[trackKey]
  ac.log("Loaded " .. #active_gate_pb .. " PB gate splits.")

  -- Reset all gate-related states for the new lap
  last_gate_crossed_index = 0
  last_pos = nil 
  manual_lap_timer = 0.0
  gate_debounce_timer = 0.0
  current_run_gate_splits = {}
  
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

-- This is our new per-frame update function, which CSP will call.
local function checkGateCrossing(dt)
  -- ===== AUTO-PLACEMENT LOGIC (RE-INTEGRATED) =====
  if auto_placement_active then
    -- Increment the timer
    auto_placement_timer = auto_placement_timer + dt
    
    
    if auto_placement_timer >= settings.auto_placement_interval then
      auto_placement_timer = 0.0 -- Reset the timer
      
      local owncar = ac.getCar(0)
      if owncar and owncar.position then
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
        ac.log("Auto-placed Gate #" .. #current_route.gates .. " for route '" .. current_route.name .. "'.")
      end
    end
    
    return -- IMPORTANT: Stop the function here so it doesn't try to time laps while placing gates
  end
  -- ==========================================================

  -- The rest of the timing logic is below, and will not run if auto_placement_active is true.
  gate_debounce_timer = math.max(0, gate_debounce_timer - dt)
  
  if #current_route.gates == 0 then return end

  local owncar = ac.getCar(0)
  if not owncar or not owncar.position then return end
  local current_pos_vec3 = owncar.position
  
  manual_lap_timer = manual_lap_timer + dt

  if not last_pos then
    last_pos = {x = current_pos_vec3.x, y = current_pos_vec3.y, z = current_pos_vec3.z}
    return
  end
  
  local next_gate_index = last_gate_crossed_index + 1
  if next_gate_index > #current_route.gates then return end
  
  local found_gate_index = -1

  -- 1. SEARCH WINDOW LOGIC: Always look for the next 3 gates.
  for i = next_gate_index, math.min(next_gate_index + 2, #current_route.gates) do
    local gate_to_check = current_route.gates[i]
    
    local gate_p1 = gate_to_check.p1; local gate_p2 = gate_to_check.p2
    local gate_vec = {x = gate_p2.x - gate_p1.x, z = gate_p2.z - gate_p1.z}
    local vec_to_last = {x = last_pos.x - gate_p1.x, z = last_pos.z - gate_p1.z}
    local side_last = gate_vec.x * vec_to_last.z - gate_vec.z * vec_to_last.x
    local vec_to_current = {x = current_pos_vec3.x - gate_p1.x, z = current_pos_vec3.z - gate_p1.z}
    local side_current = gate_vec.x * vec_to_current.z - gate_vec.z * vec_to_current.x
    
    if (side_last * side_current <= 0) and (gate_debounce_timer == 0) then
      found_gate_index = i
      break
    end
  end
  
  -- 2. GATE PROCESSING LOGIC: Run this block if we found a gate.
  if found_gate_index ~= -1 then
    if found_gate_index == 1 then
      startNewGateLap(current_route.name)
    end
    
    local lapTimeMS = manual_lap_timer * 1000
    ac.log("Gate " .. found_gate_index .. " crossed.")
    gate_debounce_timer = 0.1
    table.insert(current_run_gate_splits, lapTimeMS)

    local pb_split = active_gate_pb[found_gate_index]
    if pb_split then
      local delta = (lapTimeMS - pb_split) / 1000.0
      ui_gate_delta_text = string.format("Current Lap Delta: %+.2f", delta)
      if delta < 0 then ui_gate_delta_color = COL_GREEN else ui_gate_delta_color = COL_YELLOW end
      
      -- NEW: Update the state for the separate delta window
      live_delta_value = delta
      live_delta_color = ui_gate_delta_color -- Reuse the color we just calculated
    else
      ui_gate_delta_text = string.format("Current Lap Delta: %+.2f", 0.0)
      ui_gate_delta_color = nil
      
      -- NEW: Update the separate delta window state (no PB to compare against yet)
      live_delta_value = 0.0
      live_delta_color = nil
    end
    
    last_gate_crossed_index = found_gate_index
  else
    -- 3. OFF-ROUTE RESET LOGIC: This only runs if NO gate was found in the search window.
    if last_gate_crossed_index > 0 then -- Only check if a lap is in progress
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

        -- NEW: Also reset the separate delta window's state
        live_delta_value = nil
        live_delta_color = nil
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
local function updBestSector(trackK, idx, val, inval)
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

  if settings.refBestSectors then
  -- fastest individual sectors (theoretical)
  local src = bestSecs[key] and bestSecs[key].secs or {}
  local targetCount = sectorCountFor(trackName)
  local complete = true
  local total = 0

  for i=1,targetCount do
    local v = src[i]
    if v then
      activePB.secs[i] = v
      total = total + v
    else
      complete = false
      activePB.secs[i] = nil
    end
  end

  if complete then
    activePB.lap = total
    activePB.theoretical = true
  else
    -- don’t set lap if not all sectors available
    activePB.lap = nil
    activePB.theoretical = false
  end
  else
    -- fastest complete lap (fallback to bestSecs if none yet)
    local bl = bestLap[key]
    if bl and bl.secs then
      for i,v in ipairs(bl.secs) do activePB.secs[i]=v end
      activePB.lap = bl.lap
      activePB.theoretical = false
    else
      local src = bestSecs[key] and bestSecs[key].secs or {}
      for i,v in ipairs(src) do activePB.secs[i]=v end
      if #activePB.secs>0 then activePB.lap = sum(activePB.secs) end
      activePB.theoretical = true
    end
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
      local priorInvalid = anyTrue(current.inv, math.max(0, target-1))

      if #current.secs < target and #current.secs >= 1 then
        local computed = math.max(0, lapT - sum(current.secs))
        local finalInv = priorInvalid or lapInvalidFromServer
        current.secs[target] = computed
        current.inv[target]  = finalInv
        local updated = updBestSector(toKey(current.track), target, computed, finalInv)
        if updated then current.pbNew[target] = true end
      elseif #current.secs == target then
        local finalInv = (current.inv[target] or false) or priorInvalid or lapInvalidFromServer
        current.inv[target] = finalInv
      else
        for i=target+1,#current.secs do current.secs[i]=nil; current.inv[i]=nil; current.pbNew[i]=nil end
      end

      -- === CORRECT ORDER OF OPERATIONS ===
      last = cloneLap(current)
      if #last.secs == target then
        updBestLap(toKey(last.track), last.lap, last.secs, last.lapInv)
      end
      
      if #active_route_gates > 0 and #current_run_gate_splits == #active_route_gates then
        local trackKey = toKey(last.track)
        local old_pb_final_time = bestGateSplits[trackKey] and bestGateSplits[trackKey][#bestGateSplits[trackKey]]
        local new_final_time = current_run_gate_splits[#current_run_gate_splits]
        if not old_pb_final_time or new_final_time < old_pb_final_time then
          ac.log("New personal best gate splits saved for '" .. last.track .. "'.")
          bestGateSplits[trackKey] = cloneTable(current_run_gate_splits)
        end
      end
      
      local trackName = last.track
      current = newLapState()
      current.track = trackName
      snapshotActivePB(trackName)
      -- ===================================
      
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
  if settings.showInvalid and invalidFlag then
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

  -- The old inline delta text was removed from here. The new big delta is now at the top of windowMain.

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

local DeltaFont = ui.DWriteFont('Arial', './data')
    :weight(ui.DWriteFont.Weight.Bold)
    :style(ui.DWriteFont.Style.Normal)
    :stretch(ui.DWriteFont.Stretch.Normal)

function windowMain(dt)
  -- RUN OUR PER-FRAME GATE LOGIC
  checkGateCrossing(dt)

  -- If reference mode changed, resnapshot immediately
  if lastRefToggle ~= settings.refBestSectors then
    lastRefToggle = settings.refBestSectors
    snapshotActivePB(current.track ~= "" and current.track or last.track or "")
  end

  -- ===== DELTA DISPLAY (Standard Font, WITH COLOR) =====

  -- Title text
  ui.text("Current Lap Delta")

  -- Ensure our font exists (created once, reused after)
  DeltaFont = DeltaFont or ui.DWriteFont('Arial', './data')
      :weight(ui.DWriteFont.Weight.Bold)
      :style(ui.DWriteFont.Style.Normal)
      :stretch(ui.DWriteFont.Stretch.Normal)

  -- Draw the delta big and colored
  ui.pushFont(DeltaFont)
  local deltaFontSize = 36

  if live_delta_value ~= nil then
    local delta_text = string.format("%+.2f", live_delta_value)
-- Colour logic: yellow if positive, green if negative, white if 0
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


-- Separate Settings window (gear button)x
function windowSettings(dt)
  -- Helper to avoid nil-table crashes when counting
  local function tlen(t) return (type(t) == "table") and #t or 0 end

  ui.tabBar("SettingsTabs", function()

    -- ===== Display tab =====
    ui.tabItem("Display", function()
      ui.text("Sector Times Settings")
      ui.separator()

      if ui.checkbox("Highlight invalid labels in red", settings.showInvalid) then
        settings.showInvalid = not settings.showInvalid
      end
      if ui.checkbox("Count invalids as PB", settings.countInvalids) then
        settings.countInvalids = not settings.countInvalids
      end
      if ui.checkbox("Use fastest individual sectors (theoretical reference)", settings.refBestSectors) then
        settings.refBestSectors = not settings.refBestSectors
        snapshotActivePB(current.track ~= "" and current.track or (last and last.track or ""))
        lastRefToggle = settings.refBestSectors
      end

      ui.separator()
      if ui.button("Reset All Laps/Sectors/PBs") then
        resetAllData()
      end
    end)

    -- ===== Route Editor tab =====
    ui.tabItem("Route Editor", function()
      drawGateEditor()
    end)

    -- ===== Saves tab =====
    ui.tabItem("Saves", function()
      -- Defensive defaults so UI never crashes if globals are nil
      local cr     = current_route or { name = "", gates = {} }
      local splits = current_run_gate_splits or {}

      -- Loop & car labels
      local loopName = (cr.name ~= "" and cr.name) or (current and current.track or "") or ""
      local carKey, carLabel = getCarKeyAndLabel()

      ui.text("Loop: " .. (loopName ~= "" and loopName or "— (no route loaded)"))
      ui.text("Car:  " .. tostring(carLabel))
      ui.separator()

      -- Status lines
      local gatesCount  = tlen(cr.gates)
      local splitsCount = tlen(splits)
      ui.text(string.format("Gates in current route: %d", gatesCount))
      ui.text(string.format("Current run splits recorded: %d", splitsCount))
      ui.separator()

      -- Save button:
      -- On CSP builds without beginDisabled/endDisabled, we render the button
      -- and ignore clicks if saving isn't allowed, plus show why.
      local canSave = (gatesCount > 0 and splitsCount > 0)
      if ui.button("Save current gate lap") then
        if canSave then
          local ok, err = saveCurrentGateSnapshot()
          if not ok and err then ac.log("[Saves] Save failed: " .. tostring(err)) end
        end
      end
      if not canSave then
        if gatesCount == 0 then ui.text("• No route/gates loaded.") end
        if splitsCount == 0 then ui.text("• No recorded gate splits this run yet (finish a lap).") end
      end

      ui.sameLine()
      if ui.button("Load all PBs for this car") then
        local ok, err = loadAllBestLapsForCar() -- Call the new function
        if not ok and err then ac.log("[Saves] Load failed: " .. tostring(err)) end
      end

      ui.separator()
      -- Count how many saves exist for this loop+car
      local count, lk = 0, (toKey and toKey(loopName)) or (string.lower(loopName):gsub("%s+","_"))
      if saveIndex and saveIndex.items then
        for _, it in ipairs(saveIndex.items) do
          if it.loopKey == lk and it.carKey == carKey then count = count + 1 end
        end
      end
      ui.text(string.format("Saved snapshots for this pair: %d", count))

      -- Optional: quick utility to clear active PB for this loop (handy for testing)
      if ui.button("Clear active PB for this loop") then
        if lk and lk ~= "" then
          bestGateSplits[lk] = nil
          if active_gate_pb and active_gate_pb == bestGateSplits[lk] then active_gate_pb = nil end
          ac.log("[Saves] Cleared active PB for loop: " .. tostring(loopName))
        else
          ac.log("[Saves] No loop loaded to clear.")
        end
      end

      ui.separator()
      if ui.button("DEBUG: Force Reload Index from File") then
        ac.log("[Saves] Manual index reload triggered by user.")
        loadSaveIndex()
      end

      -- DEBUG: print what we’re matching

    end)

  end)
end



function windowTitle() return "Sector Times" end
function windowFlags()
  local f = ui.WindowFlags.AlwaysAutoResize  -- keep gear button visible; manifest controls SETTINGS
  
  return f
end