# ANU(Automatic Normalizatio Utility)

This DBMS design project will supoosed to have followings parts:

1. A tool to extract possible Canonical cover of FDs from available instance of a DB
2. DataBase Decomposition Engine based on available set of FDs
3. Query resource estimation engine based on decomposition, to select optimal decomposed schema
4. DataBase re-organisation module to convert instance of initial schema into decomposed schema

Note: Decomposition should be built like a tree sturucture,
which should be traversed to get resource estimation of Query processing
