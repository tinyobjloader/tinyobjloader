tinyobjloader
=============

[![Join the chat at https://gitter.im/syoyo/tinyobjloader](https://badges.gitter.im/Join%20Chat.svg)](https://gitter.im/syoyo/tinyobjloader?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)

[![Build Status](https://travis-ci.org/syoyo/tinyobjloader.svg)](https://travis-ci.org/syoyo/tinyobjloader)

[![wercker status](https://app.wercker.com/status/495a3bac400212cdacdeb4dd9397bf4f/m "wercker status")](https://app.wercker.com/project/bykey/495a3bac400212cdacdeb4dd9397bf4f)

[![Build status](https://ci.appveyor.com/api/projects/status/tlb421q3t2oyobcn/branch/master?svg=true)](https://ci.appveyor.com/project/syoyo/tinyobjloader/branch/master)

[![Coverage Status](https://coveralls.io/repos/github/syoyo/tinyobjloader/badge.svg?branch=master)](https://coveralls.io/github/syoyo/tinyobjloader?branch=master)

http://syoyo.github.io/tinyobjloader/

Tiny but powerful single file wavefront obj loader written in C++. No dependency except for C++ STL. It can parse 10M over polygons with moderate memory and time.

`tinyobjloader` is good for embedding .obj loader to your (global illumination) renderer ;-)

Notice!
-------

`master` branch will be replaced with `develop` branch in the near future: https://github.com/syoyo/tinyobjloader/tree/develop
`develop` branch has more better support and clean API interface for loading .obj and also it has optimized multi-threaded parser(probably 10x faster than `master`). If you are new to use `TinyObjLoader`, I highly recommend to use `develop` branch.


What's new
----------

* Mar 13, 2016 : Introduce `load_flag_t` and flat normal calculation flag! Thanks Vazquinhos!
* Jan 29, 2016 : Support n-polygon(no triangulation) and OpenSubdiv crease tag! Thanks dboogert!
* Nov 26, 2015 : Now single-header only!.
* Nov 08, 2015 : Improved API.
* Jun 23, 2015 : Various fixes and added more projects using tinyobjloader. Thanks many contributors!
* Mar 03, 2015 : Replace atof() with hand-written parser for robust reading of numeric value. Thanks skurmedel!
* Feb 06, 2015 : Fix parsing multi-material object
* Sep 14, 2014 : Add support for multi-material per object/group. Thanks Mykhailo!
* Mar 17, 2014 : Fixed trim newline bugs. Thanks ardneran!
* Apr 29, 2014 : Add API to read .obj from std::istream. Good for reading compressed .obj or connecting to procedural primitive generator. Thanks burnse!
* Apr 21, 2014 : Define default material if no material definition exists in .obj. Thanks YarmUI!
* Apr 10, 2014 : Add support for parsing 'illum' and 'd'/'Tr' statements. Thanks mmp!
* Jan 27, 2014 : Added CMake project. Thanks bradc6!
* Nov 26, 2013 : Performance optimization by NeuralSandwich. 9% improvement in his project, thanks!
* Sep 12, 2013 : Added multiple .obj sticher example.

Example
-------

![Rungholt](https://github.com/syoyo/tinyobjloader/blob/master/images/rungholt.jpg?raw=true)

tinyobjloader can successfully load 6M triangles Rungholt scene.
http://graphics.cs.williams.edu/data/meshes.xml

Use case
--------

TinyObjLoader is successfully used in ...

* bullet3 https://github.com/erwincoumans/bullet3
* pbrt-v2 https://github.com/mmp/pbrt-v2
* OpenGL game engine development http://swarminglogic.com/jotting/2013_10_gamedev01
* mallie https://lighttransport.github.io/mallie
* IBLBaker (Image Based Lighting Baker). http://www.derkreature.com/iblbaker/
* Stanford CS148 http://web.stanford.edu/class/cs148/assignments/assignment3.pdf
* Awesome Bump http://awesomebump.besaba.com/about/
* sdlgl3-wavefront OpenGL .obj viewer https://github.com/chrisliebert/sdlgl3-wavefront
* pbrt-v3 https://github.com/mmp/pbrt-v3
* cocos2d-x https://github.com/cocos2d/cocos2d-x/
* Android Vulkan demo https://github.com/SaschaWillems/Vulkan
* voxelizer https://github.com/karimnaaji/voxelizer
* Probulator https://github.com/kayru/Probulator
* OptiX Prime baking https://github.com/nvpro-samples/optix_prime_baking
* FireRays SDK https://github.com/GPUOpen-LibrariesAndSDKs/FireRays_SDK
* parg, tiny C library of various graphics utilities and GL demos https://github.com/prideout/parg
* Opengl unit of ChronoEngine https://github.com/projectchrono/chrono-opengl
* Your project here!

Features
--------

* Group(parse multiple group name)
* Vertex
* Texcoord
* Normal
* Material
  * Unknown material attributes are returned as key-value(value is string) map.
* Crease tag('t'). This is OpenSubdiv specific(not in wavefront .obj specification)


TODO
----

* [ ] Support different indices for vertex/normal/texcoord

License
-------

Licensed under 2 clause BSD.

Usage
-----

TinyObjLoader triangulate input .obj by default.
```c++
#define TINYOBJLOADER_IMPLEMENTATION // define this in only *one* .cc
#include "tiny_obj_loader.h"

std::string inputfile = "cornell_box.obj";
std::vector<tinyobj::shape_t> shapes;
std::vector<tinyobj::material_t> materials;
  
std::string err;
bool ret = tinyobj::LoadObj(shapes, materials, err, inputfile.c_str());
  
if (!err.empty()) { // `err` may contain warning message.
  std::cerr << err << std::endl;
}

if (!ret) {
  exit(1);
}

std::cout << "# of shapes    : " << shapes.size() << std::endl;
std::cout << "# of materials : " << materials.size() << std::endl;
  
for (size_t i = 0; i < shapes.size(); i++) {
  printf("shape[%ld].name = %s\n", i, shapes[i].name.c_str());
  printf("Size of shape[%ld].indices: %ld\n", i, shapes[i].mesh.indices.size());
  printf("Size of shape[%ld].material_ids: %ld\n", i, shapes[i].mesh.material_ids.size());
  assert((shapes[i].mesh.indices.size() % 3) == 0);
  for (size_t f = 0; f < shapes[i].mesh.indices.size() / 3; f++) {
    printf("  idx[%ld] = %d, %d, %d. mat_id = %d\n", f, shapes[i].mesh.indices[3*f+0], shapes[i].mesh.indices[3*f+1], shapes[i].mesh.indices[3*f+2], shapes[i].mesh.material_ids[f]);
  }

  printf("shape[%ld].vertices: %ld\n", i, shapes[i].mesh.positions.size());
  assert((shapes[i].mesh.positions.size() % 3) == 0);
  for (size_t v = 0; v < shapes[i].mesh.positions.size() / 3; v++) {
    printf("  v[%ld] = (%f, %f, %f)\n", v,
      shapes[i].mesh.positions[3*v+0],
      shapes[i].mesh.positions[3*v+1],
      shapes[i].mesh.positions[3*v+2]);
  }
}

for (size_t i = 0; i < materials.size(); i++) {
  printf("material[%ld].name = %s\n", i, materials[i].name.c_str());
  printf("  material.Ka = (%f, %f ,%f)\n", materials[i].ambient[0], materials[i].ambient[1], materials[i].ambient[2]);
  printf("  material.Kd = (%f, %f ,%f)\n", materials[i].diffuse[0], materials[i].diffuse[1], materials[i].diffuse[2]);
  printf("  material.Ks = (%f, %f ,%f)\n", materials[i].specular[0], materials[i].specular[1], materials[i].specular[2]);
  printf("  material.Tr = (%f, %f ,%f)\n", materials[i].transmittance[0], materials[i].transmittance[1], materials[i].transmittance[2]);
  printf("  material.Ke = (%f, %f ,%f)\n", materials[i].emission[0], materials[i].emission[1], materials[i].emission[2]);
  printf("  material.Ns = %f\n", materials[i].shininess);
  printf("  material.Ni = %f\n", materials[i].ior);
  printf("  material.dissolve = %f\n", materials[i].dissolve);
  printf("  material.illum = %d\n", materials[i].illum);
  printf("  material.map_Ka = %s\n", materials[i].ambient_texname.c_str());
  printf("  material.map_Kd = %s\n", materials[i].diffuse_texname.c_str());
  printf("  material.map_Ks = %s\n", materials[i].specular_texname.c_str());
  printf("  material.map_Ns = %s\n", materials[i].specular_highlight_texname.c_str());
  std::map<std::string, std::string>::const_iterator it(materials[i].unknown_parameter.begin());
  std::map<std::string, std::string>::const_iterator itEnd(materials[i].unknown_parameter.end());
  for (; it != itEnd; it++) {
    printf("  material.%s = %s\n", it->first.c_str(), it->second.c_str());
  }
  printf("\n");
}
```

Reading .obj without triangulation. Use `num_vertices[i]` to iterate over faces(indices). `num_vertices[i]` stores the number of vertices for ith face.
```c++
#define TINYOBJLOADER_IMPLEMENTATION // define this in only *one* .cc
#include "tiny_obj_loader.h"

std::string inputfile = "cornell_box.obj";
std::vector<tinyobj::shape_t> shapes;
std::vector<tinyobj::material_t> materials;
  
std::string err;
int flags = 1; // see load_flags_t enum for more information.
bool ret = tinyobj::LoadObj(shapes, materials, err, inputfile.c_str(), flags);
  
if (!err.empty()) { // `err` may contain warning message.
  std::cerr << err << std::endl;
}

if (!ret) {
  exit(1);
}

for (size_t i = 0; i < shapes.size(); i++) {

  size_t indexOffset = 0;
  for (size_t n = 0; n < shapes[i].mesh.num_vertices.size(); n++) {
    int ngon = shapes[i].mesh.num_vertices[n];
    for (size_t f = 0; f < ngon; f++) {
      unsigned int v = shapes[i].mesh.indices[indexOffset + f];
      printf("  face[%ld] v[%ld] = (%f, %f, %f)\n", n,
        shapes[i].mesh.positions[3*v+0],
        shapes[i].mesh.positions[3*v+1],
        shapes[i].mesh.positions[3*v+2]);
      
    }
    indexOffset += ngon;
  }

}
```
