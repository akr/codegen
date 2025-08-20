This sample shows how to organize project less files.

This works after 2025-08 that we implemented a feature to
save C-level API configurations into .vo files.

example/str uses three files (`str.v`, `str_api.v`, and `str_gen.v`) for `str.[ch]`.
example/str2 uses one file (`str.v`) for `str.[ch]`.
