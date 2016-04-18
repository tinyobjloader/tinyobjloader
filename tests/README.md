# Build&Test

## Use makefile

    $ make check

## Use ninja + kuroga

Assume

* ninja 1.4+
* python 2.6+

Are installed.

### Linux/MacOSX

    $ python kuroga.py config-posix.py
    $ ninja

### Windows

    > python kuroga.py config-msvc.py
    > vcbuild.bat

