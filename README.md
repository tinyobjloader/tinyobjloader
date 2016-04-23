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


What's new
----------

* XX  YY, ZZZZ : New data strcutre and API!
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
* Callback API for custom loading.


TODO
----

* [ ] Read .obj/.mtl from memory.
* [ ] Fix Python binding.
* [ ] Unit test codes.

License
-------

Licensed under MIT license.

Usage
-----

```c++
#define TINYOBJLOADER_IMPLEMENTATION // define this in only *one* .cc
#include "tiny_obj_loader.h"

std::string inputfile = "cornell_box.obj";
tinyobj::attrib_t attrib;
std::vector<tinyobj::shape_t> shapes;
std::vector<tinyobj::material_t> materials;
  
std::string err;
bool ret = tinyobj::LoadObj(&attrib, &shapes, &materials, &err, inputfile.c_str());
  
if (!err.empty()) { // `err` may contain warning message.
  std::cerr << err << std::endl;
}

if (!ret) {
  exit(1);
}

// See loader_example.cc for more details.
```


Tests
-----

Unit tests are provided in `tests` directory. See `tests/README.md` for details.
