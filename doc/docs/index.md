# TinyObjLoader documentation

T.B.W.

## Python API

T.B.W.

## Extensions

### Vertex Skinning extension.

Experimental support of vertex skinning in TinyObjLoader.

#### Vertex weights

    vw w0 w1 w2 ...

#### Normalization

Vertex weights must be normalized. i.e. summing up all weight values equal to 1.0.

Here is a valid vertex weights.

    vw 1.0 0.0 0.0 0.0
    vw 0.1 0.8 0.1 0.0

#### joints

    vj j0 j1 j2
