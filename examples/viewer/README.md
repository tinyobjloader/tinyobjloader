# Simple .obj viewer with glew + glfw3 + OpenGL

## Build on Windows.

### Requirements

* premake5
* Visual Studio 2013
* Windows 64bit
  * 32bit may work.

Put glfw3 and glew library somewhere and replace include and lib path in `premake4.lua`

Then,

    > premake5.exe vs2013
