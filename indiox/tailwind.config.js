const fs = require('fs');

function findAllRsExtensions(dir) {
  const extensions = [];
  const files = fs.readdirSync(dir);
  files.forEach(file => {
    const filePath = `${dir}/${file}`;
    const stat = fs.statSync(filePath);
    if (stat.isDirectory()) {
      extensions.push(...findAllRsExtensions(filePath));
    } else if (file.endsWith('.rs')) {
      extensions.push(filePath);
    }
  });
  return extensions;
}

module.exports = {
  content: findAllRsExtensions("./src"),
  theme: {
    //extend: {},
    container: { center: true, }
  },
  plugins: [
    //require('@tailwindcss/typography'),
    //require('@tailwindcss/forms'),
    //require('@tailwindcss/line-clamp'),
    //require('@tailwindcss/aspect-ratio'),
    require('tw-elements/dist/plugin')
  ],
  //presets: [ require('@acmecorp/tailwind-base') ],
  // https://github.com/tailwindlabs/tailwindcss/blob/master/stubs/defaultConfig.stub.js
}
