const webpack = require('webpack');

const shebang = new webpack.BannerPlugin({
  banner: "#!/usr/bin/env node\n",
  raw: true,
});

module.exports = [
    {
      name: 'warblre-node-playground',
      mode: 'production',
      target: 'node',
      output: {
        filename: './warblre-node-playground.js',
        library: 'warblre',
      },
      plugins: [
        shebang
      ],
    }
  ];