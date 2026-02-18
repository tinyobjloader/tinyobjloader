import numpy as np

from .loader import Loader, LoadException

TWO_QUADS = """
v 0 0 0
v 0 0 0
v 0 0 0
v 0 0 0
f 1 2 3 4
v 46.367584 82.676086 8.867414
v 46.524185 82.81955 8.825487
v 46.59864 83.086678 8.88121
v 46.461926 82.834091 8.953863
f 5 6 7 8
"""


def test_numpy_face_vertices_two_quads():
    # Set up.
    loader = Loader(triangulate=False)
    loader.loads(TWO_QUADS)

    shapes = loader.shapes
    assert len(shapes) == 1

    # Confidence check.
    (shape,) = shapes
    expected_num_face_vertices = [4, 4]
    assert shape.mesh.num_face_vertices == expected_num_face_vertices

    # Test.
    np.testing.assert_array_equal(shape.mesh.numpy_num_face_vertices(), expected_num_face_vertices)
