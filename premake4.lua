lib_sources = {
   "tiny_obj_loader.cc"
}

sources = {
   "test.cc",
   }

-- premake4.lua
solution "TinyObjLoaderSolution"
   configurations { "Release", "Debug" }

   if (os.is("windows")) then
      platforms { "x32", "x64" }
   else
      platforms { "native", "x32", "x64" }
   end

   -- A project defines one build target
   project "tinyobjloader"
      kind "ConsoleApp"
      language "C++"
      files { lib_sources, sources }

      configuration "Debug"
         defines { "DEBUG" } -- -DDEBUG
         flags { "Symbols" }
         targetname "test_tinyobjloader_debug"

      configuration "Release"
         -- defines { "NDEBUG" } -- -NDEBUG
         flags { "Symbols", "Optimize" }
         targetname "test_tinyobjloader"
