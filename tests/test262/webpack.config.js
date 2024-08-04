module.exports = [
  {
    name: 'warblre-node-redirect',
    mode: 'development',
    // devtool: false,
    target: 'node',
    output: {
      filename: './warblre-node-redirect.js',
      library: 'warblre',
    },
  },
  {
    name: 'warblre-browser-redirect',
    mode: 'development',
    devtool: false,
    target: 'web',
    output: {
      filename: './warblre-browser-redirect.js',
      library: 'warblre',
    },
  },
];