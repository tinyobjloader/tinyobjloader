# Demo assets

- `ferndale_studio_06_1k.hdr` — HDR environment map from
  [Poly Haven](https://polyhaven.com/a/ferndale_studio_06), licensed **CC0**
  (public domain, no attribution required). 1k Radiance HDR, 1,228,415 bytes,
  MD5 `87eb6541fcc367bce545a458c18190ec`.

The demo loads it with Three.js `RGBELoader` + `PMREMGenerator` to provide
image-based lighting for PBR/MaterialX materials. No network access is needed
at runtime.
