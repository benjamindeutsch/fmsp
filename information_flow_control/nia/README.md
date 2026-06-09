nia.py
======

Template for the project on IFC and Noninterference.
Implementation of the nia analysis presented at the lecture.

## Directory Structure

```
├── tests/
│   ├── nia/          Tests for the strict noninterference analysis, divided in positive and negative results
│   │   ├── neg/
│   │   └── pos/
│   └── abstract/     Tests for the abstract noninterference analysis (see second project task)
│       ├── neg/
│       └── pos/
├── helpers.py        Utilities and definitions to handle variables and generation of Z3 predicates
├── nia.py            Definition of the `abstraction` function for strict noninterference and test definitions
├── nia-abstract.py   Definition of the `abstraction` function for the abstract noninterference analysis (see second project task) and test definitions
├── parser.py         Parser for the WHILE language
└── whilelang.py      Definitions of the AST of the WHILE language
```

## Setup

- Python3 venv:
  ```
  python3 -m venv .venv
  source .venv/bin/activate
  pip install -r requirements.txt
  ```
- nix (with flakes enabled)
  ```
  nix develop
  ```

## Running the templates

The strict noninterference analysis can be executed with:
```
python3 nia.py
```

The abstract noninterference analysis can be executed with:
```
python3 nia-abstract.py
```

