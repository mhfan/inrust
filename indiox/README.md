
## Instructions

1. Install npm: <https://docs.npmjs.com/downloading-and-installing-node-js-and-npm>
2. Install the tailwind css cli: <https://tailwindcss.com/docs/installation>
and tw-elements package: <https://tw-elements.com/docs/standard/getting-started/quick-start/>
4. Run the following command in the root of the project to start the tailwind CSS compiler:

```bash
npm install tailwindcss tw-elements -D #-g

npx tailwindcss -i tailwind_base.css -o dist/tailwind.css -w #-m
```

Launch the Dioxus Web/Desktop app:

```bash
dx serve #--verbose
dx serve --platform web

dx serve --platform desktop #rm -rf dist
cd dist && cargo r --features desktop
```
