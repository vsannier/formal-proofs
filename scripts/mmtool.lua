#!/usr/bin/env lua

--[[ This work by Victor Sannier is released under the MIT License. --]]

-------------------------------------------------------------------------------
-- Lua and shell utilities
-------------------------------------------------------------------------------

-- Build a (sortable) array given an arbitrary table
function build_array(tbl, key_lbl, val_lbl) local arr = {}
   for key, val in pairs(tbl) do
      table.insert(arr, { [key_lbl] = key, [val_lbl] = val })
   end
   return arr
end

-- Print an error message
function eprint(message)
   io.stderr:write(string.format("[ERROR] %s\n", message))
end

-------------------------------------------------------------------------------
-- Metamath functions
-------------------------------------------------------------------------------

function get_theorems(filepath)
   local theorems = {}

   local handle = io.popen(
     "metamath"
     .. string.format(" 'read \"%s\"'", filepath)
     .. " 'set scroll continuous'"
     .. " 'show labels */linear'"
     .. " 'quit'"
   )

   for line in handle:lines() do
      line = line:gsub("%s+", " ")
      local label = string.match(line, "^%d+ (%S+) %$p$")
      if label then table.insert(theorems, label) end
   end

   handle:close()
   return theorems
end

function get_statements(filepath)
   local statements = {}

   local handle = io.popen(
     "metamath"
     .. string.format(" 'read \"%s\"'", filepath)
     .. " 'set width 9999'"
     .. " 'show statement *'"
     .. " 'quit'"
   )

   for line in handle:lines() do
      line = line:gsub("%s+", " ")
      local stmt = string.match(line, "^%d.-%$[ap] (.-) %$%=")
      if stmt then table.insert(statements, stmt) end
   end

   handle:close()
   return statements
end

function get_proven(filepath)
   local proven = {}

   local handle = io.popen(
     "metamath"
     .. string.format(" 'read \"%s\"'", filepath)
     .. " 'set width 9999'"
     .. " 'show proof */lemmon'"
     .. " 'quit'"
   )

   for line in handle:lines() do
      line = line:gsub("%s+", " ")
      local stmt = string.match(line, "^%d+ [1-9][0-9,]* %S* %$[ap] (.*)")
      if stmt then proven[stmt] = (proven[stmt] or 0) + 1 end
   end

   local statements = get_statements(filepath)
   for _, stmt in pairs(statements) do proven[stmt] = nil end

   handle:close()
   return proven
end

function compare_proven(s1, s2)
   return (s1.count > s2.count) or
      ((s1.count == s2.count) and (string.len(s1.stmt) < string.len(s2.stmt)))
end

function minimize_proofs(filepath)
   local theorems = get_theorems(filepath)

   -- Create a temporary file to hold the commands
   local tmp_filepath = os.tmpname()
   local tmp_handle = io.open(tmp_filepath, "w")
   for _, label in pairs(theorems) do
      tmp_handle:write(string.format("prove %s/override\n", label))
      tmp_handle:write("minimize_with */allow_new_axioms *\n")
      tmp_handle:write("save new_proof/compressed\n")
      tmp_handle:write("exit/force\n")
   end
   tmp_handle:close() -- Close the file to save the contents

   local handle = io.popen(
     "metamath"
     .. string.format(" 'read \"%s\"'", filepath)
     .. string.format(" 'submit \"%s\"'", tmp_filepath)
     .. string.format("  'write source \"%s.min\"/format/rewrap'", filepath)
     .. "  'quit'"
   )

   for line in handle:lines() do print(line) end

   handle:close()
   os.remove(tmp_filepath)
end

-------------------------------------------------------------------------------
-- Main program
-------------------------------------------------------------------------------

local usage = [[
Usage: metalsmith <subcommand> <database>
Subcommands: help list-theorems minimize-all find-repeats
]]

local subcommand = arg[1] or "help"
local filepath = arg[2] or "set.mm"

if subcommand == "help" then
   -- Print the usage message
   io.write(usage)
elseif subcommand == "list-theorems" then
   -- List the theorem labels in the database
   for _, label in pairs(get_theorems(filepath)) do
      print("  " .. label)
   end
elseif subcommand == "minimize-all" then
   -- Shorten proofs by using previously proven theorems
   minimize_proofs(filepath)
elseif subcommand == "find-repeats" then
   -- Find statements proven multiple times in the database
   local proven = build_array(get_proven(filepath), "stmt", "count")
   table.sort(proven, compare_proven)
   for _, stmt in pairs(proven) do
      print(string.format("%d %s", stmt.count, stmt.stmt))
   end
else
   eprint(string.format("Unknown subcommand: %s", subcommand))
end
