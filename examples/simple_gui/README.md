# Simple .obj viewer with GUI support(imgui + glew + glfw3 + OpenGL 2)

## Requirements

* cmake
* glfw3

## Build on Linux

```
$ mkdir build
$ cd build
$ cmake ..
$ make
```

## Third party licenses

* stb_image : Public domain.
* imgui(docking branch) : MIT license https://github.com/ocornut/imgui
* glad : No license?

## TODO

* [ ] Build on MSVC
* [ ] Build on MaCOSX
* [ ] Alpha texturing.
* [ ] Support per-face material.
* [ ] Use shader-based GL rendering.
* [ ] PBR shader support.
