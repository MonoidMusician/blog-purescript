const path = require("path");
const HtmlWebpackPlugin = require("html-webpack-plugin");
const HtmlWebpackHarddiskPlugin = require("html-webpack-harddisk-plugin");
const webpack = require("webpack");
const ssr = require("./ssr");
module.exports = {
	mode: "development",
	entry: "./src/index.js",
	output: {
		path: path.resolve(__dirname, "dist"),
		filename: "bundle.js",
	},
	plugins: [
		new HtmlWebpackPlugin({
			alwaysWriteToDisk: true,
			templateContent: ssr.ssr,
		}),
		new HtmlWebpackHarddiskPlugin(),
		new webpack.EnvironmentPlugin({
			LIL_GUI: "true",
		}),
	],
	module: {
		rules: [
			{
				test: /\.js$/i,
				include: path.resolve(__dirname, "src"),
				use: {
					loader: "babel-loader",
					options: {
						presets: ["@babel/preset-env"],
					},
				},
			},
			{
				test: /\.s[ac]ss$/i,
				include: [path.resolve(__dirname, "src")],
				use: ["style-loader", "css-loader", "sass-loader"],
			},
			{
				test: /\.bme/,
				type: "asset/source",
			},
			{
				test: /\.mp3/,
				type: "asset/resource",
			},
			{
				test: /\.jpg/,
				type: "asset/resource",
			},
			{
				test: /\.png/,
				type: "asset/resource",
			},
			{
				test: /\.css$/i,
				include: [path.resolve(__dirname, "src")],
				use: ["style-loader", "css-loader", "postcss-loader"],
			},
		],
	},
	devServer: {
		static: {
			directory: path.join(__dirname, "dist"),
		},
		historyApiFallback: {
			index: "index.html",
		},
	},
};
