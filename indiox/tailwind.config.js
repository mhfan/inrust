/** @type {import('tailwindcss').Config} */
module.exports = {
  content: ["./src/**/*.rs"], //"./src/**/*.{rs,html,css}"
  //mode: "all",

  theme: {
    container: { center: true, }
    //extend: {},
  },

  plugins: [
    //require('@tailwindcss/forms'),
    //require('tailwindcss-children'),
    //require('@tailwindcss/typography'),
    //require('@tailwindcss/aspect-ratio'),
    //require('@tailwindcss/line-clamp'),
    require('tw-elements/plugin.cjs'), // npm install tw-elements -D
  ],

  //presets: [ require('@acmecorp/tailwind-base') ],
  // https://github.com/tailwindlabs/tailwindcss/blob/master/stubs/defaultConfig.stub.js
  // npm install tailwindcss -D #-g // npx tailwindcss init #--full
  // npx tailwindcss -i tailwind_base.css -o assets/tailwind.css -w #-m
}
