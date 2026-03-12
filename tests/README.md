# Build&Test

## Use makefile

    $ make check

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

 
