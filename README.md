# Stella language server

An to provide language support for the [Stella language](https://fizruk.github.io/stella).

## Development

Install dependencies:

```sh
npm install
```

Generate Langium sources before running tests:

```sh
npm run langium:generate
npm test
```

The generation step creates `src/language/generated/module.js`, which is required by the Vitest focus tests.

## Public tests

The public Stella fixtures are committed under `test/public-tests-main`.
Each suite (`hw1`, `hw2`, `hw3`) contains paired `.in` and `.out` files copied from the public course test distribution. The `.in` file is parsed and type-checked, and the `.out` file lists the expected `ERROR_*` tags; an empty `.out` means the program is expected to pass.

Run the public tests with:

```sh
npm run langium:generate
npx vitest run test/public-tests-main/public-tests.test.ts
```

## Features
- Type checking
- Syntax highlighting, including inside markdown fenced block
- Semantic highlighting
- Code snippets
- Go to definition
- AST viewer
- Code extensions validation and suggestions (with quick fixes)

![AST view](./images/ast-view.png)
