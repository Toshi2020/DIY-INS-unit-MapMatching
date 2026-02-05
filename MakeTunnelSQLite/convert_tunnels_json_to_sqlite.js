const fs = require("fs");
const Database = require("better-sqlite3");

const INPUT_JSON = "tunnels.json";
const OUTPUT_DB  = "tunnels.sqlite";

//--------------------------------------------------
// SQLite 初期化
//--------------------------------------------------
if (fs.existsSync(OUTPUT_DB)) fs.unlinkSync(OUTPUT_DB);
const db = new Database(OUTPUT_DB);

db.exec(`
PRAGMA journal_mode = WAL;
PRAGMA synchronous = OFF;

CREATE TABLE segments (
	id INTEGER PRIMARY KEY,
	way_id INTEGER,
	seq INTEGER,
	lat REAL,
	lon REAL
);

CREATE TABLE  bounds (
	way_id INTEGER,
	minlat REAL,
	maxlat REAL,
	minlon REAL,
	maxlon REAL
);
`);

//--------------------------------------------------
// INSERT 文
//--------------------------------------------------
const insertSeg = db.prepare(`
INSERT INTO segments
(way_id, seq, lat, lon)
VALUES (?, ?, ?, ?)
`);

const insertBound = db.prepare(`
INSERT INTO bounds
(way_id, minlon, maxlon, minlat, maxlat)
VALUES (?, ?, ?, ?, ?)
`);

//--------------------------------------------------
// JSON 読み込み
//--------------------------------------------------
const osm = JSON.parse(fs.readFileSync(INPUT_JSON, "utf8"));

let segId = 1;

const tx = db.transaction(() => {

	for (const e of osm.elements) {
		if (e.type !== "way" || !e.geometry || e.geometry.length < 2)
			continue;

		const minlat = e.bounds.minlat;
		const maxlat = e.bounds.maxlat;
		const minlon = e.bounds.minlon;
		const maxlon = e.bounds.maxlon;

		insertBound.run(
			e.id,
			minlon, maxlon,
			minlat, maxlat
		);

		let seq = 0;
		for (let i = 0; i < e.geometry.length; i++) {
			const p = e.geometry[i];

			const info = insertSeg.run(
				e.id, seq++,
				p.lat, p.lon
			);
			segId++;
		}
	}
});

tx();

db.exec(`
CREATE INDEX idx_segments ON segments(way_id);
CREATE INDEX idx_bounds ON bounds(minlon, maxlon, minlat, maxlat);
`);

db.close();

console.log("✅ tunnels.sqlite を保存しました。");
console.log("ファイルサイズ:", fs.statSync("tunnels.sqlite").size, "bytes");
