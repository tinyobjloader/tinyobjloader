# Build&Test

## Use makefile

    $ make check

`make check` builds and runs the suite in two configurations:

* `check_default` — library defaults: no SIMD, no multithreading, no
  exceptions.
* `check_features` — `TINYOBJLOADER_USE_MULTITHREADING`,
  `TINYOBJLOADER_USE_SIMD`, and `TINYOBJLOADER_ENABLE_EXCEPTION` all enabled.

Run a single configuration with `make check_default` or `make check_features`.

Additional fuzz targets:

    $ make obj-fuzz
    $ make llvm-fuzz

## Use ninja + kuroga

Assume

* ninja 1.4+
* python 2.6+

Are installed.

### Linux/MacOSX

    $ python kuroga.py config-posix.py
    $ ninja

### Windows

Visual Studio 2013 is required to build tester.

On Windows console.

    > python kuroga.py config-msvc.py
    > vcbuild.bat


Or on msys2 bash,

    $ python kuroga.py config-msvc.py
    $ cmd //c vcbuild.bat

 
