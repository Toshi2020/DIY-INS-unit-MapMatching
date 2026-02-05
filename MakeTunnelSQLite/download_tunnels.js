const fs = require("fs");
const query = `
[out:json][timeout:180];
(
  way["highway"]["tunnel"~"yes"](area:3600382313);
);
out geom;
`;

const url = "https://overpass-api.de/api/interpreter";

async function run() {
  console.log("⏳ Overpassからトンネル道路データ取得中(1～2分かかります)...");

  const res = await fetch(url, {
	method: "POST",
	body: query,
  });

  const text = await res.text();

  // 出力確認
  if (!text.includes('"elements"')) {
	console.error("❌ Overpass のレスポンスが異常です:");
	console.log(text);
	return;
  }

  fs.writeFileSync("tunnels.json", text, "utf-8");

  console.log("✅ tunnels.json を保存しました。");
  console.log("ファイルサイズ:", fs.statSync("tunnels.json").size, "bytes");
}

run();
