package com.toshi.gpsselector;
/*****************************************************************************
*
*	GpsSelector:MyService -- 通信サービス
*
*	rev1.0	09.Oct.2021	initial revision by	Toshi
*	rev1.1	02.Mar.2022	画面のキャプチャを追加
*	rev1.2	11.Jan.2026 マップマッチングした位置情報をシリアルで返す
*
*****************************************************************************/
import android.Manifest;
import android.annotation.SuppressLint;
import android.app.Activity;
import android.app.Service;
import android.bluetooth.BluetoothAdapter;
import android.bluetooth.BluetoothDevice;
import android.bluetooth.BluetoothSocket;
import android.content.Intent;
import android.content.pm.PackageManager;
import android.database.Cursor;
import android.database.sqlite.SQLiteDatabase;
import android.database.sqlite.SQLiteException;
import android.hardware.display.DisplayManager;
import android.hardware.display.VirtualDisplay;
import android.location.Location;
import android.location.LocationManager;
import android.location.provider.ProviderProperties;
import android.os.Bundle;
import android.os.Environment;
import android.os.IBinder;
import android.app.Notification;
import android.app.NotificationChannel;
import android.app.NotificationManager;
import android.app.PendingIntent;
import android.content.Context;
import android.os.Handler;
import android.os.Looper;
import android.os.SystemClock;
import android.util.Log;

import androidx.core.content.ContextCompat;
import androidx.core.content.PermissionChecker;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.net.InetAddress;
import java.net.Socket;
import java.security.KeyStore;
import java.text.ParseException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Locale;
import java.util.TimeZone;
import java.text.SimpleDateFormat;

import android.view.Surface;
import android.widget.Toast;
import android.os.Build;
import android.content.BroadcastReceiver;
import android.content.IntentFilter;
import android.content.SharedPreferences;

import androidx.core.app.ActivityCompat;
import androidx.preference.PreferenceManager;
import java.util.UUID;

import androidx.core.app.NotificationCompat;

import com.google.android.gms.location.*;
import com.google.android.gms.location.FusedLocationProviderClient;
import com.google.android.gms.location.LocationServices;
import com.google.android.gms.location.LocationRequest;
import com.google.android.gms.location.Priority;
import android.hardware.usb.UsbDeviceConnection;
import android.hardware.usb.UsbManager;
import android.hardware.usb.UsbDevice;
import com.hoho.android.usbserial.driver.UsbSerialDriver;
import com.hoho.android.usbserial.driver.UsbSerialPort;
import com.hoho.android.usbserial.driver.UsbSerialProber;
import com.hoho.android.usbserial.util.SerialInputOutputManager;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileOutputStream;
import java.io.OutputStreamWriter;
import java.util.Calendar;

import android.media.MediaRecorder;
import android.media.projection.MediaProjection;
import android.media.projection.MediaProjectionManager;

import org.json.JSONArray;
import org.json.JSONObject;
import org.osmdroid.library.BuildConfig;
import org.osmdroid.util.GeoPoint;

import javax.net.ssl.SSLContext;
import javax.net.ssl.SSLSocket;
import javax.net.ssl.SSLSocketFactory;
import javax.net.ssl.TrustManagerFactory;
import javax.net.ssl.X509TrustManager;

import okhttp3.ConnectionSpec;
import okhttp3.OkHttpClient;
import okhttp3.Request;
import okhttp3.RequestBody;
import okhttp3.Response;
import okhttp3.MediaType;
import okhttp3.TlsVersion;

//****************************************************************************
// インスタンス作成時
//
public class MyService extends Service {
	private static final String TAG = "■MyService ";
	private static boolean fServiceRunning;		// サービス起動中フラグ
	private volatile boolean fThreadRunning;	// スレッド起動中フラグ
	private SharedPreferences sharedPref;
	private SharedPreferences.Editor sharedEdit;
	private BluetoothSocket BtSocket;
	private BluetoothDevice gpsDevice;
	private Thread gpsThread;
	private static String EndMsg = "";
	private boolean fMockEnable;
	private boolean fMockGpsIns;
	private boolean fMapMatch;
	private boolean fMockSound;
	private boolean fInsTest;
	private boolean fInsTestZ;
	private boolean fStop;
	private String mProviderNameGps, mProviderNameNet, mProviderNameFused;
	private LocationManager mLocationManager = null;
	private LocationCallback mLocationCallback;
	private int TimeAfterRxFix;
	private final int POWERON_DELAY = 100;	// 起動後Mockしない時間[s]x10

	private double ExtGpsLon, ExtGpsLat;	// 外付けGPS経度&緯度[deg]
	private double ExtGpsLonZ, ExtGpsLatZ;	// 外付けGPS経度&緯度[deg]
	private float ExtGpsV;					// 外付けGPS速度[m/s]
	private float ExtGpsVZ;					// 外付けGPS速度[m/s]
	private float ExtGpsHdop = 255.0f;		// 外付けGPS精度[HDOP]
	private float ExtGpsDir;				// 外付けGPS方位[deg]
	private float ExtGpsDirZ;				// 外付けGPS方位[deg]

	private double GpsLon, GpsLat;			// 外付けGPS本体経度&緯度[deg]
	private double GpsLonZ, GpsLatZ;		// 外付けGPS本体経度&緯度[deg]
	private float GpsDir;					// 外付けGPS本体方位[deg]
	private boolean fGpsRxLatLon;			// 外付けGPS本体経度&緯度を受信

	private double MatchLon, MatchLat;		// マッチGPS本体経度&緯度[deg]
	private static double MatchLonZ, MatchLatZ;
	private float MatchDir;					// マッチGPS本体方位[deg]

	private float bug, bug1, mydebug;		// デバッグ用変数
	private int ExtSatNum;					// 外付けGPS衛星数
	private boolean fExtGpsRxOk;			// 外付けGPS受信確定
	private boolean fExtGpsFix;				// 外付けGPS測距確定
	private boolean fExtGpsDoubt;			// 外付けGPS測距確定だが怪しい
	private boolean fCurve;					// 外付けGPSカーブ走行中
	private boolean fReverseRun;			// 外付けGPSバック走行中
	private int ExtRxTime;					// 外付けGPS受信間隔
	private final Handler mTimerHandler = new Handler(Looper.getMainLooper());
	private boolean fExtGpsUse;				// 外付けGPS使用
	private boolean fExtGpsUseZ;
	private boolean fIntGpsFix, fIntGpsFixZ;// 内部GPS測距確定
	private boolean fMain;					// メインSW
	private boolean fMockAddedGps;			// Mockプロバイダ追加済み(GPS)
	private boolean fMockAddedNet;			// Mockプロバイダ追加済み(Network)
	private boolean fMockAddedFused;		// Mockプロバイダ追加済み(Fused)
	private FusedLocationProviderClient mFusedLocationClient;
	private static String sInsMsg = "";
	private int ExtLocCount;
	private static final int MAX_READ_SIZE = 16 * 1024;
	private byte[] UsbBuff;
	private int ProductID, VendorID;
	private boolean fBluetooth;
	private boolean fBluetoothEnabled;
	private UsbDevice mDevice = null;
	private static UsbSerialPort mSerialPort;
	private boolean fMockForceDisable;

	// シリアル受信バッファ
	private final StringBuilder SerialBuff = new StringBuilder();
	private UsbManager mUsbManager;
	private SerialInputOutputManager mSerialIoManager;
	private int DataType;	// 受信データのフォーマット 1=NMEA, 2=Log
	private int TimeoutDelay;
	private long LastTime;
	private static boolean fScreenOff;
	private static final String ACTION_USB_PERMISSION =
			"com.toshi.gpsselector.USB_PERMISSION";
	private static final int DATAMAX = 21;	// 1行のログデータ個数

	// ファイル関連
	private final String sEncode = "SJIS";
	private File LogFile, DocDir, Mp4File;
	private String sLogFile, sDocDir, sMp4File;
	private String sLogFilePathName, sMp4FilePathName;
	private BufferedWriter bufferedWriter;
	private static long LogLine;
	private static boolean fLogging, fLoggingZ;
	
	// Map関連
	private static MapInfo mMapInfo = new MapInfo();
	private static MapInfo mMapInfo0 = new MapInfo();
	// マップマッチング関連
	private static List<List<GeoPoint>> Roads = null;
	private volatile boolean isLoadingRoads = false;	// loading中
	private static int TxCount = 0;
	private boolean fMatchData;		// マップマッチデータあり
	private boolean fMapMatching;	// INSユニットがマップマッチした
	private double MatchLatErr, MatchLonErr, MatchDirErr;
	private static int MatchRoadIndex = -1;
	private float MatchRoadLen;
	private SQLiteDatabase tunnelDb;	// トンネルDB
	class Projection {
		GeoPoint pt;
		boolean outSegment;
	}
	private boolean fbegin = false;		// 初期化したらtrue
	private long BeginTime;				// 開始時間

	// キャプチャ関連
	private int mDisplayWidth, mDisplayHeight;
	private int mScreenDensity;
	private static Intent mResultData;
	private MediaProjectionManager mpManager;
	private MediaProjection mProjection;
	private MediaRecorder mMediaRecorder;
	private VirtualDisplay mVirtualDisplay;
	private boolean fCapture;
	
	public MyService() {
	}

	/*------------------------------------------------------------------------
	画面のオフを受けるためのレシーバー
	------------------------------------------------------------------------*/
	private BroadcastReceiver screenStatusReceiver = new BroadcastReceiver() {
		@Override
		public void onReceive(Context context, Intent intent) {
			// 画面が消えたら
			if (intent.getAction().equals(Intent.ACTION_SCREEN_OFF)) {
				// 画面がオフになったフラグを立てる
				fScreenOff = true;
			}
		}
	};
	//------------------------------------------------------------------------
	// インスタンス作成時の処理
	//------------------------------------------------------------------------
	@Override
	public void onCreate() {
		super.onCreate();
		Log.d(TAG,"onCreate");
		sharedPref = PreferenceManager.getDefaultSharedPreferences(this);
		sharedEdit = sharedPref.edit();

		// LocationManager取得
		mLocationManager = 
			(LocationManager)getSystemService(Context.LOCATION_SERVICE);

		// 疑似ロケーションプロバイダ名
		mProviderNameGps = LocationManager.GPS_PROVIDER;
		mProviderNameNet = LocationManager.NETWORK_PROVIDER;
		mProviderNameFused = "fused";
		// Fused用Locationクライアント
		mFusedLocationClient = LocationServices.
								getFusedLocationProviderClient(this);

		// GPS位置情報コールバック
		mLocationCallback = new LocationCallback() {
			@Override
			public void onLocationResult(LocationResult locationResult) {
				if (locationResult == null) {
					return;
				}
				Location location = locationResult.getLastLocation();
				if (location == null) {
					return;
				}
//				ToastShow("精度" + location.getAccuracy());
				// Mockしていないなら
				if (!fExtGpsUse) {
					// 精度が20未満なら内部GPSが受信Fixとみなす
					fIntGpsFix = (location.getAccuracy() < 20.0f);
				}
				if (!fIntGpsFixZ && fIntGpsFix) {
//					ToastShow("★内部GPSが確定しました");
				}
//				else if (fIntGpsFixZ && !fIntGpsFix) {
//					ToastShow("☆内部GPSがロストしました");
//				}
				fIntGpsFixZ = fIntGpsFix;
			}
		};
		// GPS許可が設定されていなければ
		if (PermissionChecker.checkSelfPermission(this,
				Manifest.permission.ACCESS_FINE_LOCATION) !=
				PermissionChecker.PERMISSION_GRANTED) {
			ToastShow("GPSが許可されていません。");
			stopSelf();
			return;
		} else {
			// 位置情報の取得条件を設定
			LocationRequest locationRequest =
					new LocationRequest.Builder(
							Priority.PRIORITY_HIGH_ACCURACY, 1000)
							.setMinUpdateIntervalMillis(1000)
							.build();
			// 位置情報用のコールバックを設定
			mFusedLocationClient.requestLocationUpdates(locationRequest,
					mLocationCallback,
					Looper.getMainLooper());
		}

		// UsbManagerの取得
		mUsbManager = (UsbManager)getSystemService(Context.USB_SERVICE);
		UsbBuff = new byte[MAX_READ_SIZE];

		// ブロードキャストレシーバー登録
		IntentFilter filter = new IntentFilter();
		filter.addAction(Intent.ACTION_SCREEN_OFF);
		registerReceiver(screenStatusReceiver, filter);

		// ログファイル作成用ドキュメントディレクトリ
//		File dir = getExternalFilesDir(Environment.DIRECTORY_DOCUMENTS);
		DocDir = android.os.Environment.getExternalStoragePublicDirectory(
					Environment.DIRECTORY_DOCUMENTS);
//		if (dir == null) {
//			ToastShow("保存先取得失敗");
//			return;
//		}
//		DocDir = dir;
		sDocDir = DocDir.getPath();
		if (sDocDir == null) {	// F/S:設定されていない場合
			sDocDir = android.os.Environment.getExternalStorageDirectory().
							getPath()+"/Documents";
			DocDir = new File(sDocDir);
		}
		// トンネルDBの読み取り
		File dbFile = new File(DocDir, "tunnels.sqlite");
		if (!dbFile.exists()) {
			tunnelDb = null;
		} else {
			tunnelDb = SQLiteDatabase.openDatabase(
				dbFile.getAbsolutePath(),
				null,
				SQLiteDatabase.
				OPEN_READONLY | SQLiteDatabase.NO_LOCALIZED_COLLATORS);
		ToastShow(EndMsg + "道路データベースを読み込みました");
		}
	}
	//------------------------------------------------------------------------
	// サービス終了時
	//------------------------------------------------------------------------
	@Override
	public void onDestroy() {
		super.onDestroy();
		Log.d(TAG,"onDestroy");

		// タイマー終了
		mTimerHandler.removeCallbacks(TimerTask);

		// スレッド＆通信終了
		EndCom();

		// 位置情報用のコールバックを解除
		if (mFusedLocationClient != null && mLocationCallback != null) {
			mFusedLocationClient.removeLocationUpdates(mLocationCallback);
		}
		// 全疑似ロケーションプロバイダ終了
		RemoveMockProvider();

		// ブロードキャストレシーバー解除
		if (screenStatusReceiver != null) {
			unregisterReceiver(screenStatusReceiver);
		}

		ToastShow(EndMsg + " サービス終了");
		EndMsg = "";

		mResultData = null;
		fIntGpsFix = false;
		fIntGpsFixZ = false;
		fScreenOff = false;
		LastTime = 0L;
		fServiceRunning = false;	// サービス非作動
	}
	//------------------------------------------------------------------------
	// bind要求時(使われない)
	//------------------------------------------------------------------------
	@Override
	public IBinder onBind(Intent intent) {
		// TODO: Return the communication channel to the service.
		throw new UnsupportedOperationException("Not yet implemented");
	}
	//------------------------------------------------------------------------
	// サービス開始要求時
	//------------------------------------------------------------------------
	@SuppressWarnings("deprecation")
	@Override
	public int onStartCommand(Intent intent, int flags, int startId) {

		Log.d(TAG,"StartCommand");

		// プリファレンスから設定値を読み込む
		// 作動要求
		fMain = sharedPref.getBoolean("START_SW", false);
		fMockEnable = sharedPref.getBoolean("MOCK", false);
		fMapMatch = sharedPref.getBoolean("MOCK1", false);
		fInsTest = sharedPref.getBoolean("MOCK2", false);

		ProductID = sharedPref.getInt("PRODUCT_ID", 0);
		VendorID = sharedPref.getInt("VENDOR_ID", 0);
		fBluetooth = (ProductID == 0 && VendorID == 0);
		fScreenOff = false;

		// 再起動された時の処理
		if (intent == null) {
			if (!fMain) {
				stopSelf();
				return Service.START_NOT_STICKY;
			}
			return Service.START_STICKY;
		}

		// キャプチャ関連のデータ受け取る
		Intent i;
		if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.TIRAMISU) {
			i = intent.getParcelableExtra("data", Intent.class);
		} else {
			i = intent.getParcelableExtra("data");
		}
		if (i != null) {
			mResultData = i;
		}
		mDisplayWidth = intent.getIntExtra("width", 768);
		mDisplayHeight = intent.getIntExtra("height", 1024);
		mScreenDensity = intent.getIntExtra("dpi", 160);
		fCapture = intent.getBooleanExtra("capture", false);

		// 許可がないなら先には進めない
		if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.R) {
			if (!Environment.isExternalStorageManager()) {
				return Service.START_NOT_STICKY;
			}
		}
		if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.S) {
			if (ContextCompat.checkSelfPermission(
				this, Manifest.permission.BLUETOOTH_CONNECT)  !=
					PackageManager.PERMISSION_GRANTED) {

				return Service.START_NOT_STICKY;
			}
		}
		if (Build.VERSION.SDK_INT < Build.VERSION_CODES.TIRAMISU) {
			if (ContextCompat.checkSelfPermission(
				this, Manifest.permission.WRITE_EXTERNAL_STORAGE)  !=
					PackageManager.PERMISSION_GRANTED) {

				return Service.START_NOT_STICKY;
			}
		}
		if (ContextCompat.checkSelfPermission(
				this, Manifest.permission.ACCESS_FINE_LOCATION) !=
					PackageManager.PERMISSION_GRANTED) {

			return Service.START_NOT_STICKY;
		}
		// 作動要求？
		if (fMain) {
			// 今作動していないなら
			if (!fServiceRunning) {
				LastTime = System.currentTimeMillis();
				fServiceRunning = true;	// サービス作動中
				// サービスをforegroundに
				startForegroundService();

				EndMsg = "";
				// 仮の現在値アプリになっているか
				AddMockProvider();		// 全疑似ロケーションプロバイダ開始
//				if (!fMockAddedGps) {	// Android10(API29)以上だと原則不可
				if (!fMockAddedFused) {
					ToastShow("仮の現在値アプリとして設定されていません");
				}
				RemoveMockProvider();	// 最初は外しておく

				// 通信＆スレッド開始
				if (BeginCom() == false) {
					return Service.START_NOT_STICKY;
				}
				ToastShow("サービス始動");
				TimeoutDelay = 3;	// 開始後しばらくはタイムアウト表示なし
				TimeAfterRxFix = 0;
				fMockForceDisable = true;

				// タイマー開始
				mTimerHandler.postDelayed(TimerTask, 100);
			}
		}
		BeginTime = System.currentTimeMillis();	// 開始時間
		return Service.START_STICKY;
	}
	//------------------------------------------------------------------------
	// サービスをforegroundに
	//------------------------------------------------------------------------
	private void startForegroundService() {

		String title = getString(R.string.app_name);
		String channelId = "service_notification";

		// メインActivityを起動させるためのインテント
		PendingIntent launchIntent =
			PendingIntent.getActivity(
				this,
				0,
				new Intent(this, MainActivity.class),
				PendingIntent.FLAG_UPDATE_CURRENT |
				PendingIntent.FLAG_IMMUTABLE);

		// Notification Builderの作成
		NotificationManager notificationManager =
					(NotificationManager)getSystemService(
				Context.NOTIFICATION_SERVICE);
		NotificationCompat.Builder builder;
		if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
			// Notification Channelの設定
			notificationManager.createNotificationChannel(
				new NotificationChannel(
					channelId,
					title,
					NotificationManager.IMPORTANCE_HIGH));
			builder = new NotificationCompat.Builder(this, channelId);
		} else {
			builder = new NotificationCompat.Builder(this, "");
		}

		// Notificationの作成
		Notification notification = builder
			.setContentIntent(launchIntent)
			.setSmallIcon(R.drawable.ic_launcher_foreground)
			.setAutoCancel(true)
			.setContentTitle(title + " サービス")
			.setContentText("タップしてメイン画面を表示")
			.setWhen(System.currentTimeMillis())
			.build();

		startForeground(1, notification);
	}
//****************************************************************************
// Bluetooth & USBシリアル通信関連
//
	//------------------------------------------------------------------------
	// Bluetoothオープン
	//------------------------------------------------------------------------
	@SuppressWarnings("deprecation")
	private boolean OpenBluetooth() {

		// BTデバイスアドレス
		String deviceAddress = sharedPref.getString("DEVICE", null);
		if (deviceAddress == null) {
			EndMsg = "Bluetoothデバイスが設定されていません";
			return false;
		}
		// BTアダプター
		BluetoothAdapter bluetoothAdapter = null;
		if (Build.VERSION.SDK_INT < Build.VERSION_CODES.S ||
			checkSelfPermission(Manifest.permission.BLUETOOTH_CONNECT)
				== PackageManager.PERMISSION_GRANTED) {

			bluetoothAdapter = BluetoothAdapter.getDefaultAdapter();
		}
		if (bluetoothAdapter == null) {
			EndMsg = "Bluetoothアダプターが取得できません";
			return false;
		}
		fBluetoothEnabled = bluetoothAdapter.isEnabled();	// BTオン？
		// BTデバイス
		gpsDevice = bluetoothAdapter.getRemoteDevice(deviceAddress);
		if (gpsDevice == null) {
			EndMsg = "Bluetoothデバイスが取得できません";
			return false;
		}
		return true;
	}
	//------------------------------------------------------------------------
	// Bluetoothクローズ
	//------------------------------------------------------------------------
	private void CloseBluetooth() {
		if (BtSocket != null) {
			try {
				BtSocket.close();
			} catch(Exception e){
				DebugToastShow("Err=1");
			}
		}
	}
	//------------------------------------------------------------------------
	// USBシリアルオープン
	//------------------------------------------------------------------------
	private boolean OpenSerial() {

		// デバイスの取得
		for (UsbDevice dev : mUsbManager.getDeviceList().values()) {
			if (dev.getVendorId() == VendorID &&
				dev.getProductId() == ProductID) {
				mDevice = dev;
				break;	// ここでループを抜ける
			}
		}
		if (mDevice == null) {
			EndMsg = "USBデバイスが取得できません";
			return false;
		}

		// ドライバーの取得
		UsbSerialDriver mDriver = UsbSerialProber.getDefaultProber().
				probeDevice(mDevice);
		if (mDriver == null) {
			EndMsg = "USBドライバが取得できません";
			return false;
		}
		// USB許可が一度もない場合
		if (!mUsbManager.hasPermission(mDriver.getDevice())) {
			// 許可ダイアログの表示
			PendingIntent permissionIntent = PendingIntent.getBroadcast(
				this, 0, new Intent(ACTION_USB_PERMISSION),
				PendingIntent.FLAG_IMMUTABLE);
			mUsbManager.requestPermission(mDevice, permissionIntent);
			AutoStop("USBの使用を許可してください");
			stopSelf();		// サービスは終了
			return false;
		}
		// コネクションの取得
		UsbDeviceConnection mConnection = mUsbManager.openDevice(mDevice);
		if (mConnection == null &&
				!mUsbManager.hasPermission(mDriver.getDevice())) {
			EndMsg = "USB使用許可がありません";
			return false;
		}
		if (mConnection == null) {
			EndMsg = "USBシリアルコネクションが取得できません";
			return false;
		}
		// シリアルポートを取得(1つ目のポートに決め打ち)
		mSerialPort = mDriver.getPorts().get(0);
		// シリアルポートのオープン
		try {
			mSerialPort.open(mConnection);
			mSerialPort.setParameters(
//				19200,
				115200,
				8,
				UsbSerialPort.STOPBITS_1,
				UsbSerialPort.PARITY_NONE);
		} catch (IOException e) {
			EndMsg = "シリアルポートのオープンエラーです";
			return false;
		}
		return true;
	}
	//------------------------------------------------------------------------
	// USBシリアルクローズ
	//------------------------------------------------------------------------
	private void CloseSerial() {

		if (mSerialPort != null) {		// シリアルを設定済みなら
			try {
				mSerialPort.close();	// ポートを閉じる
			} catch (IOException e) {
				ToastShow("シリアルポートのクローズエラーです");
			}
			mSerialPort = null;
		}
	}
	//------------------------------------------------------------------------
	// Bluetooth接続と読み取りのためのスレッド
	//------------------------------------------------------------------------
	private class ConnectGps extends Thread {
		@Override
		public void run() {
			fThreadRunning = true;
			try {
				BtSocket = 
					gpsDevice.createRfcommSocketToServiceRecord(
					UUID.fromString("00001101-0000-1000-8000-00805F9B34FB"));
				BtSocket.connect();
				InputStream inStream = BtSocket.getInputStream();
				InputStreamReader isr =
						new InputStreamReader(inStream,"US-ASCII");
				BufferedReader br = new BufferedReader(isr);
				String line;
				while (!isInterrupted() && (line = br.readLine()) != null) {
//					Log.d(TAG, line);
					boolean fok = false;
					if (line.length() > 0) {	// 空行を除去
						line = line.replace("\r\n", "");// 行末のCRLFを削除
						if (line.charAt(0) == '$') {
							// NMEAエンコード&Mock
							fok = ExtNmeaEncode(line);
						} else {
							// Logデータエンコード&Mock
							fok = ExtLogEncode(line);
						}
						if (fok) {
							fExtGpsRxOk = true;		// 外付けGPS受信確定
							MapMatching();			// マップマッチング
							WriteLogFile(line);		// ログ書き込み
						}
					}
				}
				EndMsg = "";	// 終了要因メッセージをクリア
			} catch (IOException e) {
				ToastShow("Bluetooth接続できません");
			}
			fThreadRunning = false;
		}
	}
	//------------------------------------------------------------------------
	// USB接続と読み取りのためのスレッド
	//------------------------------------------------------------------------
	private class ConnectGpsUSB extends Thread {
		@Override
		public void run() {
			fThreadRunning = true;
			try {
				while (!isInterrupted()) {
					int len = mSerialPort.read(UsbBuff, MAX_READ_SIZE);
					if (len > 0) {
						String str = new String(UsbBuff);
						str = str.substring(0, len);
						int index = str.indexOf("\n");
						// 改行文字が含まれていたら
						if (index >= 0) {
							// 改行までを取り出す
							SerialBuff.append(str.substring(0,index + 1));
							String line = SerialBuff.toString();
//							Log.d(TAG, line);
							line = line.replace("\r\n", "");//行末のCRLFを削除
							boolean fok = false;
							if (line.length() > 0) {	// 空行を除去
								if (line.charAt(0) == '$') {
									// NMEAエンコード&Mock
									fok = ExtNmeaEncode(line);
								} else {
									// Logデータエンコード&Mock
									fok = ExtLogEncode(line);
								}
								if (fok) {
									fExtGpsRxOk = true;	// 外付けGPS受信確定
									MapMatching();		// マップマッチング
									WriteLogFile(line);	// ログ書き込み
								}
							}
							// バッファクリア
							SerialBuff.setLength(0);
							// 残りをバッファに格納
							SerialBuff.append(str.substring(index + 1));
						} else {
							// 受信した文字をバッファに追加
							SerialBuff.append(str);
						}
					}
				}
				EndMsg = "";	// 終了要因メッセージをクリア
			} catch (IOException e) {
				ToastShow("USB接続できません");
			}
			fThreadRunning = false;
		}
	}
	//------------------------------------------------------------------------
	// 通信＆スレッド開始
	//------------------------------------------------------------------------
	private boolean BeginCom() {
		ExtRxTime = 0;			// タイムアウトカウンタクリア
		fExtGpsRxOk = false;	// 外付けGPS未受信とする
		fExtGpsFix = false;		// 外付けGPS未確定とする
		fExtGpsUse = false;		// 強制的に内部GPS使用に
		DataType = 0;			// 受信データタイプクリア
		if (fBluetooth) {
			// Bluetooth準備
			if (!OpenBluetooth()) {				// BT開始できないなら
				ToastShow(EndMsg);
				return false;					// ここまで
			}
			if (fBluetoothEnabled) {			// BTオンなら
				gpsThread = new ConnectGps();	// Bluetooth受信スレッド
			}
		} else {
			// USBシリアル準備
			if (!OpenSerial()) {				// シリアル開始できないなら
				ToastShow(EndMsg);
				return false;					// ここまで
			}
			gpsThread = new ConnectGpsUSB();	// USB受信スレッド
		}
		if (gpsThread != null) {
			gpsThread.start();	// スレッド起動
		}
		return true;
	}
	//------------------------------------------------------------------------
	// スレッド＆通信終了
	//------------------------------------------------------------------------
	private void EndCom() {
		if (gpsThread != null) {
			gpsThread.interrupt();		// スレッド停止をリクエスト
			// スレッド終了を待つ
			if (fThreadRunning) {
				try {
					gpsThread.join(100);
				} catch (InterruptedException e) {
					DebugToastShow("Err=2");
				}
			}
			gpsThread = null;
		}
		// Bluetoothクローズ
		CloseBluetooth();

		// シリアルクローズ
		CloseSerial();

		// ログファイルクローズ
		CloseLogFile();
		fLogging = false;
	}
	//------------------------------------------------------------------------
	// 通信再起動
	//------------------------------------------------------------------------
	private void RestartCom() {
		EndCom();				// いったん終了して
		BeginCom();				// 再開する
	}
	//------------------------------------------------------------------------
	// サービス停止要求
	//------------------------------------------------------------------------
	private void AutoStop(String msg) {
		EndMsg = msg;
		sharedEdit.putBoolean("START_SW", false).apply();
	}
//****************************************************************************
// NMEAエンコード&Mock
//
	private boolean ExtNmeaEncode(String nmea) {
		if (!SumCheck(nmea)) {	// サムが正しくないなら
			return false;		// ここまで
		}

		String[] NmeaS = nmea.split(",");	// カンマで分割
		DataType = 1;	// NMEAフォーマット
		// NMEAパーサー
		if (NmeaS[0].equalsIgnoreCase("$GNRMC") ||
				NmeaS[0].equalsIgnoreCase("$GPRMC")) {
			ExtRxTime = 0;		// 外付けGPS受信間隔クリア
			ExtGpsLat = parseNmeaLatitude(NmeaS[3], NmeaS[4]);
			ExtGpsLon = parseNmeaLongitude(NmeaS[5], NmeaS[6]);
			ExtGpsV = parseNmeaSpeed(NmeaS[7], "N");
			if (!fStop) {	// 今走行中
				if (ExtGpsV <= 0.0f) {	// 停止した？
					fStop = true;		// 停止フラグ=true
				}
			} else {		// 今停止中
				if (ExtGpsV > 0.1f) {	// 走行した？
					fStop = false;		// 停止フラグ=false
				}
			}
			if (NmeaS[8] == null || NmeaS[8].isEmpty()) {
				ExtGpsDir = 0.0f;
			} else {
				ExtGpsDir = Float.parseFloat(NmeaS[8]);
			}
			fGpsRxLatLon = true;	// GPS本体の緯度経度を受信
			// 使わないが念のため値を入れておく
			GpsLat = ExtGpsLat;
			GpsLon = ExtGpsLon;
			GpsDir = ExtGpsDir;
			// 外付けGPSを使うなら
			if (fExtGpsUse) {
				// (これらの関数はMockされていなければ何もしない)
				// 疑似ロケーションを設定(GPS)
				MockSet(fMockAddedGps, mProviderNameGps,
						ExtGpsLat, ExtGpsLon, ExtGpsDir, ExtGpsV,
						ExtGpsHdop, ExtSatNum);
				// 疑似ロケーションを設定(Network)
				MockSet(fMockAddedNet, mProviderNameNet,
						ExtGpsLat, ExtGpsLon, ExtGpsDir, ExtGpsV,
						ExtGpsHdop, ExtSatNum);
				// 疑似ロケーションを設定(fused)
				MockSet(fMockAddedFused, mProviderNameFused,
						ExtGpsLat, ExtGpsLon, ExtGpsDir, ExtGpsV,
						ExtGpsHdop, ExtSatNum);
			}
			MakeExtGpsMsg();		// 表示用データの作成
		} else if (NmeaS[0].equalsIgnoreCase("$GNGGA") ||
					NmeaS[0].equalsIgnoreCase("$GPGGA")) {
			// 衛星数
			if (NmeaS[7] == null || NmeaS[7].isEmpty()) {
				ExtSatNum = 0;
			} else {
				ExtSatNum = Integer.parseInt(NmeaS[7]);
			}
			if (ExtSatNum > 2) {	// 確定
				fExtGpsFix = true;	// 外付けGPS確定
			} else {
				fExtGpsFix = false;	// 外付けGPS未確定
			}
			fExtGpsDoubt = (ExtSatNum == 2);	// 精度悪化でのINS中は2
			// 精度(HDOP)
			if (NmeaS[8] == null || NmeaS[8].isEmpty()) {
				ExtGpsHdop = 255.0f;
			} else {
				ExtGpsHdop = Float.parseFloat(NmeaS[8]);
				fMapMatching = (int)ExtGpsHdop == 254;
			}
		}
		return true;
	}
	//------------------------------------------------------------------------
	// NMEAサムチェック
	//------------------------------------------------------------------------
	private boolean SumCheck(String buf) {
		int c = 0, sum;
		int len = buf.length();
		sum = hex2dec(buf.charAt(len - 2)) * 16 + 
							hex2dec(buf.charAt(len - 1));
		for (int i = 1; i < len - 3; i++) {
			c ^= buf.charAt(i);
		}
		sum &= 0xff;
		c &= 0xff;
		return (c == sum);
	}
	// 16進文字を10進数値に変換
	private int hex2dec(char a) {
		if (a >= 'A' && a <= 'F') {
			return a - 'A' + 10;
		} else if (a >= 'a' && a <= 'f') {
			return a - 'a' + 10;
		} else {
			return a - '0';
		}
	}
//****************************************************************************
// Logデータエンコード&Mock	ログデータの並びを変えたら修正する必要あり
//
//		0:time,1:Vreal,2:GpsVreal,3:AyRaw,4:VspC,5:YawRaw,
//		6:G経度,7:G緯度,8:I経度,9:I緯度,
//		10:GpsYaw,11:Yaw,12:Yofst,13:RollRaw,
//		14:G方位,15:I方位,16:YgainP,17:YgainM,18:PitchRaw,19:HDOP,20:Stat

	private boolean ExtLogEncode(String line) {
		String[] s = line.split(",");	// カンマで分割

		// データが全てそろっていなければ
		if (s.length != DATAMAX) {
			return false;			// ここまで
		}
		for (int i = 0; i < DATAMAX; i++) {	// 空白のデータがあるなら
			if (s[i] == null || s[i].equals("")) {
				return false;		// ここまで
			}
		}
		DataType = 2;	// Logフォーマット
		ExtRxTime = 0;	// 外付けGPS受信間隔クリア

		try {
			int stat = Integer.parseInt(s[20]);
			fStop = (stat & 0x01) != 0;			// 停止中
			fExtGpsFix = (stat & 0x02) != 0;	// GPS確定
			fExtGpsDoubt = (stat & 0x04) != 0;	// GPS疑わしい
			fCurve = (stat & 0x08) != 0;		// カーブ中
			fReverseRun = (stat & 0x10) != 0;	// バック中
			fMapMatching = (stat & 0x20) != 0;	// マップマッチング中

			ExtGpsLat = Double.parseDouble(s[9]) / 10000000.0d;
			ExtGpsLon = Double.parseDouble(s[8]) / 10000000.0d;
			ExtGpsV = Float.parseFloat(s[1]) / 3.6f;
			ExtGpsDir = Float.parseFloat(s[15]);
			bug = Float.parseFloat(s[16]);
			bug1 = Float.parseFloat(s[17]);
			ExtSatNum = Integer.parseInt(s[13]);
			ExtGpsHdop = Float.parseFloat(s[19]);

			if (!fExtGpsFix) {		// 外付けGPS未確定
				ExtSatNum = 1;		// なら衛星数=1としておく
			}
			if (fExtGpsDoubt) {		// GPS疑わしい
				ExtSatNum = 2;		// なら衛星数=2としておく
			}
			GpsLat = Double.parseDouble(s[7]) / 10000000.0d;
			GpsLon = Double.parseDouble(s[6]) / 10000000.0d;
			GpsDir = Float.parseFloat(s[14]);
			if (fReverseRun) {
				GpsDir = Add180(GpsDir);
			}
		} catch (Exception e) {
			DebugToastShow("Err=3");
			return false;
		}

		MakeExtGpsMsg();		// 表示用データの作成

		// 外付けGPSを使うなら
		if (fExtGpsUse) {
			// (これらの関数はMockされていなければ何もしない)
			// HdopにSNRを入れたので強制的にHDOP=1.0とする
			// 疑似ロケーションを設定(GPS)
			MockSet(fMockAddedGps, mProviderNameGps,
					ExtGpsLat, ExtGpsLon, ExtGpsDir, ExtGpsV,
					/*ExtGpsHdop*/ 1.0f, ExtSatNum);
			// 疑似ロケーションを設定(Network)
			MockSet(fMockAddedNet, mProviderNameNet,
					ExtGpsLat, ExtGpsLon, ExtGpsDir, ExtGpsV,
					/*ExtGpsHdop*/ 1.0f, ExtSatNum);
			// 疑似ロケーションを設定(fused)
			MockSet(fMockAddedFused, mProviderNameFused,
					ExtGpsLat, ExtGpsLon, ExtGpsDir, ExtGpsV,
					/*ExtGpsHdop*/ 1.0f, ExtSatNum);
		}
		return true;
	}

	//------------------------------------------------------------------------
	//	180deg反転
	//	書式 ret = Add180(float deg)
	//
	//	float ret;	方位[deg]
	//	float deg;	方位[deg]
	//------------------------------------------------------------------------
	private float Add180(float deg)
	{
		deg += 180.0f;			// 180deg反転
		if (deg >= 360.0f)
		{
			deg -= 360.0f;
		}
		return deg;
	}
	//------------------------------------------------------------------------
	// 外付けGPS表示データの作成
	//------------------------------------------------------------------------
	private final String dtype[] = {"[--]", "[NMEA] ", "[LOG] "};
	private final String htype[] = {"\nHDOP:", "\nHDOP:", "\nSNR:"};
	private void MakeExtGpsMsg() {
		String msg;

		// 外付けGPS表示データ
		ExtLocCount++;
		msg = dtype[DataType] + Indicator(ExtLocCount) + "\nGPS：";
		if (!fExtGpsRxOk) {			// 外部GPSからの受信が確定していないなら
			msg += "×未受信";
		} else if (fExtGpsDoubt) {	// 外部GPSが確定しているが疑わしいなら
			msg += "▲精度悪化";
		} else if (fExtGpsFix) {	// 外部GPSが確定しているなら
			msg += "■確定";
		} else {
			msg += "□ロスト";		// 外部GPSが確定していないなら
		}				
		msg += fExtGpsUse ? "\nMock：■ON" : "\nMock：□OFF";
		if (DataType == 2) {	// Logフォーマットなら
			msg +=	"\n緯度：  " + String.format("%.5f", ExtGpsLat) +
					"\n経度：" + String.format("%.5f", ExtGpsLon) +
					"\n方位：" + String.format("%.1f", ExtGpsDir);
			if (fCurve) {
				msg += "【カーブ】";
			}
			msg += "\n速度：" + String.format("%.1f", ExtGpsV * 3.6f) +
					"\t\tbug  ：" + String.format("%.4f", bug) +
					"\nSNR：" + String.format("%.1f", ExtGpsHdop) +
					"\t\tbug1：" + String.format("%.4f", bug1) +
					"\n衛星：" + String.format("%d", ExtSatNum);
		} else {
			msg +=	"\n緯度：  " + String.format("%.5f", ExtGpsLat) +
					"\n経度：" + String.format("%.5f", ExtGpsLon) +
					"\n方位：" + String.format("%.1f", ExtGpsDir) +
					"\n速度：" + String.format("%.1f", ExtGpsV * 3.6f) +
					"\nHDOP：" + String.format("%.2f", ExtGpsHdop) +
					"\n衛星：" + String.format("%d", ExtSatNum);
		}
		msg += fMatchData ? "\t\t\tマッチ：■" :
							"\t\t\tマッチ：□";
		msg += fMapMatching ? "■" :
							  "□";
		sInsMsg = msg;
		mMapInfo0.lat = ExtGpsLat;
		mMapInfo0.lon = ExtGpsLon;
		mMapInfo0.dir = ExtGpsDir;
		mMapInfo0.sat = ExtSatNum;
		mMapInfo0.gpslat = GpsLat;
		mMapInfo0.gpslon = GpsLon;
		mMapInfo0.gpsdir = GpsDir;
		mMapInfo0.fmatch = fMatchData;
		mMapInfo0.fmatching = fMapMatching;
//		mMapInfo0.matchlat = MatchLat;
//		mMapInfo0.matchlon = MatchLon;
		mMapInfo0.matchdir = MatchDir;
		mMapInfo0.speed = ExtGpsV * 3.6f;
		mMapInfo = mMapInfo0;
	}
	//------------------------------------------------------------------------
	// インジケータ文字を返す
	private final String p[] = {"・","＊","⦿","◎","○","◎","⦿","＊"};

	private String Indicator(int count) {
		if (count < 0) {
			count *= -1;
		}
		return p[count % p.length];
	}
	//------------------------------------------------------------------------
	// メインとのやり取り
	//------------------------------------------------------------------------
	// サービス実行中かどうか
	public static boolean IsServiceRunning() {
		return fServiceRunning;
	}
	// 外付けGPSの表示用データ
	public static String GetStrIns() {
		return sInsMsg;
	}
	// 画面がオフしたかどうか
	public static boolean IsScreenOff() {
		return fScreenOff;
	}
	// ログした行数
	public static long GetLogLine() {
		return LogLine;
	}
	// ログ開始要求
	public static void ReqLogStart() {
		fLogging = true;
	}
	// ログ停止要求
	public static void ReqLogStop() {
		fLogging = false;
	}
	// ロギング中か？
	public static boolean IsLogging() {
		return fLogging;
	}
	// マップに表示するための情報
	public static MapInfo GetMapInfo() {
		return mMapInfo;
	}
	// キャプチャ許可を受け取り済みか
	public static boolean IsGetResult() {
		return mResultData != null;
	}
	// マップマッチするための道路情報
	public static List<List<GeoPoint>> GetRoads() {
		return Roads;
	}
	// マップマッチした道路インデックス
	public static int getMatchRoadIndex() {
		return MatchRoadIndex;
	}
//****************************************************************************
// 疑似ロケーション
//
	//------------------------------------------------------------------------
	// 全疑似ロケーションプロバイダ開始
	//------------------------------------------------------------------------
	private void AddMockProvider() {
		if (!fMockAddedGps) {
			fMockAddedGps = AddMockProviderCore(mProviderNameGps);
		}
		if (!fMockAddedNet) {
			fMockAddedNet = AddMockProviderCore(mProviderNameNet);
		}
		if (!fMockAddedFused) {
			fMockAddedFused = AddMockProviderFused();
		}
	}
	//------------------------------------------------------------------------
	// 疑似ロケーションプロバイダ開始共通部分
	//------------------------------------------------------------------------
	private boolean AddMockProviderCore(String name) {
		boolean ret;
		try {
			mLocationManager.addTestProvider(
				name,	// name
				false,	// requiresNetwork
				false,	// requiresSatellite
				false,	// requiresCell
				false,	// hasMonetaryCost
				true,	// supportsAltitude
				true,	// supportsSpeed
				true,	// supportsBearing
				ProviderProperties.POWER_USAGE_HIGH,	// powerRequirement
				ProviderProperties.ACCURACY_FINE);		// accuracy
			mLocationManager.setTestProviderEnabled(name, true);
			ret = true;	// Mockプロバイダが組み込まれた
		} catch (Exception e) {
			DebugToastShow("Err=4");
			ret = false;
		}
		return ret;
	}
	//------------------------------------------------------------------------
	// Fused疑似ロケーションプロバイダ開始
	//------------------------------------------------------------------------
	@SuppressLint("MissingPermission")
	private boolean AddMockProviderFused() {
		boolean ret = false;
		if (mFusedLocationClient != null) {
			try {
				mFusedLocationClient.setMockMode(true);
				ret = true;
			} catch (Exception e) {
				DebugToastShow("Err=5");
			}
		}
		return ret;
	}
	//------------------------------------------------------------------------
	// 全疑似ロケーションプロバイダ終了
	//------------------------------------------------------------------------
	private void RemoveMockProvider() {
		if (fMockAddedGps) {
			RemoveMockProviderGps();
		}
		if (fMockAddedNet) {
			RemoveMockProviderNet();
		}
		if (fMockAddedFused) {
			RemoveMockProviderFused();
		}
		fMockAddedGps = false;
		fMockAddedNet = false;
		fMockAddedFused = false;
	}
	//------------------------------------------------------------------------
	// GPS疑似ロケーションプロバイダ終了
	//------------------------------------------------------------------------
	private void RemoveMockProviderGps() {
		try {
			mLocationManager.removeTestProvider(mProviderNameGps);
		} catch (Exception e) {
			DebugToastShow("Err=6");
		}
	}
	//------------------------------------------------------------------------
	// Network疑似ロケーションプロバイダ終了
	//------------------------------------------------------------------------
	private void RemoveMockProviderNet() {
		try {
			mLocationManager.removeTestProvider(mProviderNameNet);
		} catch (Exception e) {
			DebugToastShow("Err=7");
		}
	}
	//------------------------------------------------------------------------
	// Fused疑似ロケーションプロバイダ終了
	//------------------------------------------------------------------------
	@SuppressLint("MissingPermission")
	private void RemoveMockProviderFused() {
		if (mFusedLocationClient != null) {
			try {
				mFusedLocationClient.setMockMode(false);
			} catch (Exception e) {
				DebugToastShow("Err=8");
			}
		}
	}
	//------------------------------------------------------------------------
	// 疑似ロケーションをセット(GPS, Network, Fused)
	//------------------------------------------------------------------------
	@SuppressLint("MissingPermission")
	private void MockSet(boolean flag, String name, double lat, double lon,
				float bearing, float speed, float hdop, int sat) {

		// 現在組み込まれているなら
		if (flag) {
			if (sat <= 2) {	// INS中は
				sat = 11;		// 適当な数に置き換え
				hdop = 1.1f;
			}
			Location mockLocation = new Location(name);
			mockLocation.setLatitude(lat);	// 緯度[deg]
			mockLocation.setLongitude(lon);	// 経度[deg]
			mockLocation.setAltitude(100.0);// 高度[m]
			mockLocation.setTime(System.currentTimeMillis());// 時刻
			mockLocation.setElapsedRealtimeNanos(			// 起動後経過時間
					SystemClock.elapsedRealtimeNanos());
			mockLocation.setAccuracy(hdop * 10.0f);// 精度[m]
			mockLocation.setBearing(bearing);	// 方位[deg]
			mockLocation.setSpeed(speed);		// 速度[m/s]

			// 衛星の数←Google NAVIで必要
			Bundle bundle = mockLocation.getExtras();
			if (bundle == null) {
				bundle = new Bundle();
			}
			bundle.putInt("satellites", sat);	// NAVIでは0以外が必要
			mockLocation.setExtras(bundle);

			// ロケーションデータをセット
			if (name.equals(mProviderNameFused)) {
				mFusedLocationClient.setMockLocation(mockLocation);
			} else {
				mLocationManager.setTestProviderLocation(name, mockLocation);
			}
		}
	}
//****************************************************************************
// NMEAパーサーヘルパー
// https://github.com/freshollie/UsbGps4Droidより
//
	//------------------------------------------------------------------------
	// 緯度を[deg]に変換
	//------------------------------------------------------------------------
	private double parseNmeaLatitude(String lat, String orientation) {
		double latitude = 35.6796388;
		try {
			if (lat != null && orientation != null && !lat.equals("") &&
					!orientation.equals("")) {
				double temp1 = Double.parseDouble(lat);
				double temp2 = Math.floor(temp1 / 100);
				double temp3 = (temp1 / 100 - temp2) / 0.6;
				if (orientation.equals("S")) {
					latitude = -(temp2 + temp3);
				} else if (orientation.equals("N")) {
					latitude = (temp2 + temp3);
				}
			}
		} catch (Exception e) {
			DebugToastShow("Err=9");
		}
		return latitude;
	}
	//------------------------------------------------------------------------
	// 経度を[deg]に変換
	//------------------------------------------------------------------------
	private double parseNmeaLongitude(String lon, String orientation) {
		double longitude = 139.7686040;
		try {
			if (lon != null && orientation != null && !lon.equals("") &&
					!orientation.equals("")) {
				double temp1 = Double.parseDouble(lon);
				double temp2 = Math.floor(temp1 / 100);
				double temp3 = (temp1 / 100 - temp2) / 0.6;
				if (orientation.equals("W")) {
					longitude = -(temp2 + temp3);
				} else if (orientation.equals("E")) {
					longitude = (temp2 + temp3);
				}
			}
		} catch (Exception e) {
			DebugToastShow("Err=10");
		}
		return longitude;
	}
	//------------------------------------------------------------------------
	// 速度を[m/s]に変換
	//------------------------------------------------------------------------
	private float parseNmeaSpeed(String speed, String metric) {
		float meterSpeed = 0.0f;
		try {
			if (speed != null && metric != null && !speed.equals("") &&
					!metric.equals("")) {
				float temp1 = Float.parseFloat(speed) / 3.6f;
				if (metric.equals("K")) {
					meterSpeed = temp1;
				} else if (metric.equals("N")) {
					meterSpeed = temp1 * 1.852f;
				}
			}
		} catch (Exception e) {
			DebugToastShow("Err=11");
		}
		return meterSpeed;
	}
	//------------------------------------------------------------------------
	// NMEA時間を[ms]に変換
	//------------------------------------------------------------------------
	private long parseNmeaTime(String time) {
		long timestamp = 0;
		@SuppressLint("SimpleDateFormat")
		SimpleDateFormat fmt = new SimpleDateFormat("HHmmss.SSS");
		fmt.setTimeZone(TimeZone.getTimeZone("UTC"));

		try {
			if (time != null && !time.equals("")) {
				long now = System.currentTimeMillis();
				long today = now - (now % 86400000L);
				long temp1;

				// sometime we don't have millisecond in the time string,
				// so we have to reformat it
				temp1 = fmt.parse(String.format((Locale) null,
							"%010.3f", Double.parseDouble(time))).getTime();
				long temp2 = today + temp1;
				// if we're around midnight we could have a problem...
				if (temp2 - now > 43200000L) {
					timestamp = temp2 - 86400000L;
				} else if (now - temp2 > 43200000L) {
					timestamp = temp2 + 86400000L;
				} else {
					timestamp = temp2;
				}
			}
		} catch (ParseException e) {
			DebugToastShow("Err=12");
			Log.e(TAG,"Error while parsing NMEA time", e);
		}
		Log.d(TAG, "Timestamp from gps = " + String.valueOf(timestamp) +
			" System clock says " + System.currentTimeMillis());
		return timestamp;
	}
//****************************************************************************
// マップマッチング関連
//
	//------------------------------------------------------------------------
	// マップマッチングしてデータを送信
	//------------------------------------------------------------------------
	private static final double MATCHFILT = 1.0d;	// INSユニット側と同じ値
	private void MapMatching() {

		// テストモードが変化したか最初の1回目なら送信
		if (fInsTestZ != fInsTest || !fbegin) {
			SendCommand();
			fbegin = true;
		}
		fInsTestZ = fInsTest;

		// GPSが変化したら
		if (GpsLatZ != GpsLat || GpsLonZ != GpsLon)
		{
			TxCount = 0;
		}
		GpsLatZ = GpsLat;
		GpsLonZ = GpsLon;

		// マップマッチング実行条件
		boolean frun =
			// NMEAフォーマット(1s)なら毎回
			(DataType == 1 && fGpsRxLatLon) ||
			// Logフォーマットなら10回に1回
			(DataType == 2 && TxCount == 0);

		if (TxCount != 0) {
			TxCount--;
		}
		if (frun) {
			TxCount = 9;
		} else {
			return;
		}

		fGpsRxLatLon = false;	// GPS緯度経度を受信フラグクリア
		// デフォルドではINS結果をスルー
		MatchLat = ExtGpsLat;
		MatchLon = ExtGpsLon;
		MatchDir = ExtGpsDir;
		fMatchData = false;

		// 将来と現在のINS位置がRoadsの範囲内か(ROADがnullならfalse)
		boolean inside = isInsideRoadArea(ExtGpsLat, ExtGpsLon, ExtGpsDir);

		// マップマッチするモードで現在ロード最中でなくて範囲外ならば
		if (fMapMatch && (!fExtGpsFix || fExtGpsDoubt) &&
					!isLoadingRoads && !inside) {
			runOverpass(ExtGpsLat, ExtGpsLon);	// 道路情報を取得
		}

		// マップマッチングによる緯度経度を求める
		GeoPoint inspos = new GeoPoint(ExtGpsLat, ExtGpsLon);
		GeoPoint insposz = new GeoPoint(ExtGpsLatZ, ExtGpsLonZ);

		GeoPoint match, fixed;
		// 範囲内なら
		if (Roads != null && inside) {
			// マップマッチング
			match = snapToRoad(inspos, Roads, ExtGpsDir);

			if (match == inspos) {
				fixed = match;
			} else {
				// マップマッチ目標地点(平均車速で移動したとする)
				fixed = pointAlongLine(insposz, match,
							(ExtGpsVZ + ExtGpsV)/ 2.0);
			}
		} else {
			// 範囲外 or ロード中 → 暫定で生INSを使用
			fixed = inspos;
			match = inspos;
		}
		// マップマッチング結果の緯度経度
		double matchlat = match.getLatitude();	// 生のマップマッチ地点
		double matchlon = match.getLongitude();
		double mlat = fixed.getLatitude();		// 車速補正後のINS目標地点
		double mlon = fixed.getLongitude();

		// マッチング目標位置表示用データ
		mMapInfo0.matchlat = mlat;
		mMapInfo0.matchlon = mlon;

		// マップマッチング距離変化と方位
		float[] result = new float[3];	// 0:距離 1:方位
		Location.distanceBetween(MatchLatZ, MatchLonZ, matchlat, matchlon,
								result);
		float mdist = result[0];	// マップマッチ距離の変化分
		float mdir = result[1];		// マップマッチ方位
		if (mdir < 0) mdir += 360.0;

		// マップマッチするモードで現在ロード最中でなくて
		// 範囲内で車速があるのに変化がない
		if (fMapMatch && (!fExtGpsFix || fExtGpsDoubt) && !isLoadingRoads &&
					 inside && ExtGpsV > 10.0 && mdist == 0.0) {
			runOverpass(ExtGpsLat, ExtGpsLon);	// 道路情報を再取得
		}

		// マップマッチング位置とINS位置の緯度経度の差分
		MatchLatErr = mlat - ExtGpsLat;
		MatchLonErr = mlon - ExtGpsLon;
		// マップマッチング位置とINS位置の距離
		Location.distanceBetween(mlat, mlon, ExtGpsLat, ExtGpsLon, result);
		float midist = result[0];		// 距離の差分

		// マップマッチング方位とINS方位の差分
		MatchDirErr = ((mdir - ExtGpsDir + 540.0) % 360.0) - 180.0;
		double diff = Math.abs(MatchDirErr);

		// マップマッチングを要求されていて
		// GPSがロストか不確かでRoadデータ範囲内かつ
		// マップマッチ方位とINS方位のずれが大きくないかつ
		// マップマッチ位置の変化が車速に対して妥当かつ
		// マップマッチ位置とINS位置の距離が車速に対して妥当かつ
		// マッチ候補の道路長が短くない(橋梁下などを排除)かつ
		// 車速が出ている
		if (fMapMatch &&
				(!fExtGpsFix || fExtGpsDoubt) && inside &&
				diff < 90.0 &&
				mdist > 0.0 && mdist <= (ExtGpsV * 2.0 + 5.0) &&
				midist <= (ExtGpsV * 2.0 + 5.0) &&
				MatchRoadLen >= 50.0 &&
				ExtGpsV >= (7.0 / 3.6)) {
			// INSユニットでマップマッチ結果を使う
			MatchLat = mlat;
			MatchLon = mlon;
			MatchDir = mdir;
			fMatchData = true;
		} else {
			MatchLat = 0;
			MatchLon = 0;
			MatchDir = 0;
			fMatchData = false;
		}
		// マップマッチング結果を送信
		SendMatchError(fMatchData, MatchLatErr, MatchLonErr, MatchDirErr);

		ExtGpsLatZ = ExtGpsLat;
		ExtGpsLonZ = ExtGpsLon;
		ExtGpsDirZ = ExtGpsDir;
		ExtGpsVZ = ExtGpsV;
		MatchLatZ = matchlat;
		MatchLonZ = matchlon;

		// マップマッチング中ならINSユニット側と同じ補正を行っておく
		if (fMapMatch && fMatchData && fMapMatching)
		{
			// INS位置補正量
			double latcal = MatchLatErr * MATCHFILT;
			double loncal = MatchLonErr * MATCHFILT;
			// INS位置をマップマッチ位置に徐々に一致させる
			ExtGpsLatZ += latcal;
			ExtGpsLonZ += loncal;
		}
	}
	//------------------------------------------------------------------------
	// n秒後の推定位置を求める
	//------------------------------------------------------------------------
	private Location predictLocation(double lat, double lon,
						double speedMps, double bearingDeg, float n) {

		double R = 6378137.0; // 地球半径(m)
		double distance = speedMps * n; // n秒後の移動距離(m)

		double bearingRad = Math.toRadians(bearingDeg);
		double latRad = Math.toRadians(lat);
		double lonRad = Math.toRadians(lon);

		double newLatRad = Math.asin(
			Math.sin(latRad) * Math.cos(distance / R) +
			Math.cos(latRad) * Math.sin(distance / R) * Math.cos(bearingRad));

		double newLonRad = lonRad + Math.atan2(
			Math.sin(bearingRad) * Math.sin(distance / R) * Math.cos(latRad),
			Math.cos(distance / R) - Math.sin(latRad) * Math.sin(newLatRad));

		Location future = new Location("");
		future.setLatitude(Math.toDegrees(newLatRad));
		future.setLongitude(Math.toDegrees(newLonRad));
		return future;
	}
	//------------------------------------------------------------------------
	// 直線a-b上でaからの距離がcの地点のGeoPoint
	//------------------------------------------------------------------------
	private GeoPoint pointAlongLine(GeoPoint a, GeoPoint b, double c) {
		// 地球半径（m）
		final double R = 6378137.0;

		double lat1 = Math.toRadians(a.getLatitude());
		double lon1 = Math.toRadians(a.getLongitude());
		double lat2 = Math.toRadians(b.getLatitude());
		double lon2 = Math.toRadians(b.getLongitude());

		// a→b の大円距離（メートル）
		double d = 2 * R * Math.asin(Math.sqrt(
				Math.pow(Math.sin((lat2 - lat1) / 2), 2)
				+ Math.cos(lat1) * Math.cos(lat2)
				* Math.pow(Math.sin((lon2 - lon1) / 2), 2)));

		// b が a と同じ点なら a を返す
		if (d == 0) return a;

		// a→b の進行方向（bearing）
		double y = Math.sin(lon2 - lon1) * Math.cos(lat2);
		double x = Math.cos(lat1) * Math.sin(lat2)
				 - Math.sin(lat1) * Math.cos(lat2) * Math.cos(lon2 - lon1);
		double bearing = Math.atan2(y, x);

		// 進む比率 f
		double f = c / d;

		// 球面の前方位置計算
		double lat = Math.asin(
				Math.sin(lat1) * Math.cos(c / R)
				+ Math.cos(lat1) * Math.sin(c / R) * Math.cos(bearing));

		double lon = lon1 + Math.atan2(
				Math.sin(bearing) * Math.sin(c / R) * Math.cos(lat1),
				Math.cos(c / R) - Math.sin(lat1) * Math.sin(lat));

		return new GeoPoint(Math.toDegrees(lat), Math.toDegrees(lon));
	}
	//------------------------------------------------------------------------
	// 現在の位置がRoadsの範囲内かをチェックする
	//------------------------------------------------------------------------
	private boolean isInsideRoadArea(double lat, double lon, float insDir) {
		if (Roads == null || Roads.isEmpty()) return false;

		for (List<GeoPoint> road : Roads) {
			for (int i = 0; i < road.size() - 1; i++) {

				GeoPoint a = road.get(i);
				GeoPoint b = road.get(i + 1);

				// セグメント方位
				float[] r = new float[2];
				Location.distanceBetween(
					a.getLatitude(), a.getLongitude(),
					b.getLatitude(), b.getLongitude(),
					r
				);
				float segDir = r[1];
				if (segDir < 0) segDir += 360;

				// 方向差
				float diff = Math.abs((segDir - insDir + 540) % 360 - 180);

				// 距離差
				float[] dist = new float[1];
				Location.distanceBetween(lat, lon,
						a.getLatitude(), a.getLongitude(), dist);
				// 距離と方向の両方が一致
				if (dist[0] < 250 && diff < 30) {
					return true;
				}
			}
		}
		return false;
	}
	//------------------------------------------------------------------------
	// DBからRoadを得るかloadRoadsを別スレッドで実行
	//------------------------------------------------------------------------
	private long lastOverpassTime = 0; // 最後に呼んだ時刻（ミリ秒）

	private void runOverpass(double lat, double lon) {

		long now = System.currentTimeMillis();

		// 起動後1分以内か
		// 前回実行から30s経過していなければ実行しない
		if (now - BeginTime < 60000L ||
			now - lastOverpassTime < 30000L) {
			return; // フェールセーフ：過剰呼び出し防止
		}

		if (isLoadingRoads) return; // 連続リクエスト防止
		isLoadingRoads = true;		// 現在取得中
		lastOverpassTime = now;		// 実行時刻を記録

		// 非同期で呼ぶ（UIスレッドを塞がない）
		new Thread(() -> {
			try {
				List<List<GeoPoint>> newRoads;

				// トンネルSQLデータを読み込み済みでテストモードでないなら
				if (tunnelDb != null && !fInsTest) {
					// SQLからデータを得る
					newRoads = readRoads(lat, lon);

				// トンネルSQLデータがないかテストモードなら
				} else {
					// 通信でデータを得る
					newRoads = loadRoads(lat, lon);
				}
				Roads = newRoads;

			} catch (Exception e) {
				e.printStackTrace();

			} finally {
				isLoadingRoads = false;
				String msg = "所要時間=" +
					(System.currentTimeMillis() - lastOverpassTime) +
					"[ms]";
				ToastShow(msg);
			}
		}).start();
	}
	//------------------------------------------------------------------------
	// SQLite DBから道路情報を取得
	//------------------------------------------------------------------------
	private List<List<GeoPoint>> readRoads(double lat, double lon) {

		ToastShow("道路を検索します");

		GeoPoint rawPt = new GeoPoint(lat, lon);

		// 検索半径（1km）
		double delta = 0.01; // 約1km
		String sql =
			"SELECT DISTINCT way_id " +
			"FROM bounds " +
			"WHERE minlat <= ? AND maxlat >= ? " +
			"  AND minlon <= ? AND maxlon >= ?";

		String[] args = new String[] {
			String.valueOf(lat + delta),
			String.valueOf(lat - delta),
			String.valueOf(lon + delta),
			String.valueOf(lon - delta)};

		Cursor c = null;
		try {
			c = tunnelDb.rawQuery(sql, args);
		} catch (SQLiteException e) {
			Log.e("DB", "SQL error", e);
		}
		if (c == null) {
			return Roads;
		}

		// way_id を一意に集める
		HashSet<Integer> waySet = new HashSet<>();
		while (c.moveToNext()) {
			waySet.add(c.getInt(0));
		}
		c.close();

		List<List<GeoPoint>> wayList = new ArrayList<>();

		// way_nodes → polyline に変換
		for (int wayId : waySet) {
			List<GeoPoint> line = loadWayNodes(wayId);
			if (line.size() >= 2) {
				wayList.add(line);
			}
		}

		// Overpass と同じ：末端一致マージ
		return mergeSegments(wayList);
	}
	//------------------------------------------------------------------------
	// SQLite → polyline 読み出し
	//------------------------------------------------------------------------
	private List<GeoPoint> loadWayNodes(int wayId) {
		List<GeoPoint> out = new ArrayList<>();

		Cursor c = null;
		try {
			c = tunnelDb.rawQuery(
				"SELECT lat, lon FROM segments WHERE way_id=? ORDER BY seq",
				new String[]{String.valueOf(wayId)}
				);
		} catch (SQLiteException e) {
			Log.e("DB", "SQL error", e);
		}
		if (c == null) {
			return null;
		}

		while (c.moveToNext()) {
			out.add(new GeoPoint(c.getDouble(0), c.getDouble(1)));
		}
		c.close();
		return out;
	}
	//------------------------------------------------------------------------
	// Overpassにアクセスして道路情報を取得
	//------------------------------------------------------------------------
	private List<List<GeoPoint>> loadRoads(double lat, double lon)
		throws Exception {

		ToastShow("道路データを受信します");

		OkHttpClient client = enableTls12(new OkHttpClient());

		String url = "https://overpass-api.de/api/interpreter";

		String query;
		if (fInsTest) {	// テスト時は主要道路
			query =
				"[out:json];" +
					"way(around:1000," + lat + "," + lon + ")" +
					"[highway~\"primary|trunk|secondary|tertiary\"];" +
					"out geom;";
		} else {	// 通常はトンネルのみ
			query =
				"[out:json];" +
					"way(around:1000," + lat + "," + lon + ")[highway]" +
					"[tunnel=yes];" +
					"out geom;";
		}

		RequestBody body = RequestBody.create(
			query,
			MediaType.parse("text/plain"));

		Request request = new Request.Builder()
			.url(url)
			.post(body)
			.build();

		Response res = client.newCall(request).execute();
		String json = res.body().string();

		return parseOverpassRoads(json);
	}
	//------------------------------------------------------------------------
	// パース（OSMの道路はnod の配列）
	//------------------------------------------------------------------------
	private List<List<GeoPoint>> parseOverpassRoads(String json)
		throws Exception {

		JSONObject obj = new JSONObject(json);
		JSONArray elements = obj.getJSONArray("elements");

		// まずは普通にパースする
		List<List<GeoPoint>> result = new ArrayList<>();

		for (int i = 0; i < elements.length(); i++) {
			JSONObject el = elements.getJSONObject(i);
			if (!el.getString("type").equals("way")) continue;

			JSONArray geom = el.getJSONArray("geometry");
			List<GeoPoint> line = new ArrayList<>();

			for (int j = 0; j < geom.length(); j++) {
				JSONObject p = geom.getJSONObject(j);
				line.add(new GeoPoint(p.getDouble("lat"),p.getDouble("lon")));
			}
			result.add(line);
		}
		// セグメント末端一致マージ処理
		return mergeSegments(result);
	}
	//------------------------------------------------------------------------
	// セグメント末端一致マージ処理
	//------------------------------------------------------------------------
	private List<List<GeoPoint>> mergeSegments(List<List<GeoPoint>> result) {

		boolean merged = true;
		while (merged) {
			merged = false;

			outer:
			for (int i = 0; i < result.size(); i++) {
				List<GeoPoint> A = result.get(i);
				GeoPoint aStart = A.get(0);
				GeoPoint aEnd	= A.get(A.size() - 1);

				for (int j = 0; j < result.size(); j++) {
					if (i == j) continue;
					List<GeoPoint> B = result.get(j);
					GeoPoint bStart = B.get(0);
					GeoPoint bEnd	= B.get(B.size() - 1);

					// A.end == B.start
					if (equalsPoint(aEnd, bStart)) {
						A.addAll(B.subList(1, B.size()));
						result.remove(j);
						merged = true;
						break outer;
					}
					// B.end == A.start
					if (equalsPoint(bEnd, aStart)) {
						B.addAll(A.subList(1, A.size()));
						result.remove(i);
						merged = true;
						break outer;
					}
					// A.start == B.end
					if (equalsPoint(aStart, bEnd)) {
						B.addAll(A.subList(1, A.size()));
						result.remove(i);
						merged = true;
						break outer;
					}
					// A.end == B.end → reverse(B)
					if (equalsPoint(aEnd, bEnd)) {
						Collections.reverse(B);
						A.addAll(B.subList(1, B.size()));
						result.remove(j);
						merged = true;
						break outer;
					}
					// A.start == B.start → reverse(A)
					if (equalsPoint(aStart, bStart)) {
						Collections.reverse(A);
						A.addAll(B.subList(1, B.size()));
						result.remove(j);
						merged = true;
						break outer;
					}
				}
			}
		}

		return result;
	}
	//------------------------------------------------------------------------
	// 緯度経度一致の判定（誤差対策）
	//------------------------------------------------------------------------
	private boolean equalsPoint(GeoPoint p1, GeoPoint p2) {
		return Math.abs(p1.getLatitude()  - p2.getLatitude())  < 1e-11 &&
			   Math.abs(p1.getLongitude() - p2.getLongitude()) < 1e-11;
	}
	//------------------------------------------------------------------------
	// 道路の方位を算出
	//------------------------------------------------------------------------
	private float segmentBearing(GeoPoint a, GeoPoint b) {
		float[] r = new float[2];
		Location.distanceBetween(
			a.getLatitude(), a.getLongitude(),
			b.getLatitude(), b.getLongitude(),
			r);
		float bearing = r[1];
		if (bearing < 0) bearing += 360;
		return bearing;
	}
	//------------------------------------------------------------------------
	// 最近接道路セグメントへ投影（スナップポイント算出）
	//------------------------------------------------------------------------
	private GeoPoint snapToRoad(GeoPoint rawPt, List<List<GeoPoint>> roads,
					float insDir) {

		double minDist = Double.MAX_VALUE;
		GeoPoint best = rawPt;
		MatchRoadIndex = -1;

		for (int r = 0; r < roads.size(); r++) {
			List<GeoPoint> road = roads.get(r);

			double roadMinScore = Double.MAX_VALUE;
			GeoPoint roadBest = null;

			for (int i = 0; i < road.size() - 1; i++) {
				GeoPoint a = road.get(i);
				GeoPoint b = road.get(i + 1);

				// セグメント方位
				float segDir = segmentBearing(a, b);

				// INS方向とセグメント方向の差分
				float diff = Math.abs((segDir - insDir + 540) % 360 - 180);

				// 進行方向と大きく違う道路は除外
				if (diff > 30) continue;

				// セグメントへの直交投影
				Projection proj = projectPointToSegment(rawPt, a, b);
				// セグメント外へ投影されたなら使わない
//				if (proj.outSegment) continue;

				// そこまでの距離
				double d = proj.pt.distanceToAsDouble(rawPt);
				// 評価値
				double score = d + (diff / 45.0) * 20.0;
				if (score < roadMinScore) {
					roadMinScore = score;
					roadBest = proj.pt;
				}
			}

			if (roadBest != null && roadMinScore < minDist) {
				minDist = roadMinScore;
				best = roadBest;
				MatchRoadIndex = r;
			}
		}
		// マッチ対象の道路があるなら
		if (MatchRoadIndex != -1) {
			// 端点
			List<GeoPoint> matchroad = roads.get(MatchRoadIndex);
			GeoPoint a = matchroad.get(0);
			GeoPoint b = matchroad.get(matchroad.size() - 1);
			// 端点間の距離(おおむねwayの長さ)
			float[] ret = new float[1];
			Location.distanceBetween(
				a.getLatitude(), a.getLongitude(),
				b.getLatitude(), b.getLongitude(),
				ret);
			MatchRoadLen = ret[0];	// マッチ候補の道路長
		} else {
			MatchRoadLen = 0.0f;
		}
		return best;
	}
	//------------------------------------------------------------------------
	// セグメントへの直交投影（数学処理）
	//------------------------------------------------------------------------
	private Projection projectPointToSegment(
			GeoPoint p, GeoPoint a, GeoPoint b) {

		double ax = a.getLongitude();
		double ay = a.getLatitude();
		double bx = b.getLongitude();
		double by = b.getLatitude();
		double px = p.getLongitude();
		double py = p.getLatitude();

		double abx = bx - ax;
		double aby = by - ay;

		double t = ((px - ax) * abx + (py - ay) * aby) /
				   (abx * abx + aby * aby);

		// セグメント範囲を外れるなら端点にスナップ
		boolean fout = t < 0 || t > 1;
		if (t < 0) t = 0;
		if (t > 1) t = 1;

		double sx = ax + t * abx;
		double sy = ay + t * aby;

		Projection proj = new Projection();
		proj.pt = new GeoPoint(sy, sx);
		proj.outSegment = fout;

		return proj;
	}
	//------------------------------------------------------------------------
	// マップマッチ結果を送信
	//------------------------------------------------------------------------
	private void SendMatchError(boolean f,
							double lat, double lon, double dir) {
		try {
			String msg = String.format(Locale.US,
				"LON=%d,LAT=%d,DIR=%f,%d\r\n",
				(long)(lon * 10000000.0d),
				(long)(lat * 10000000.0d),
				(float)dir,
				f ? 1 : 0);
			byte[] data = msg.getBytes("US-ASCII");

			if (fBluetooth && BtSocket != null && BtSocket.isConnected()) {
				BtSocket.getOutputStream().write(data);
			} else if (!fBluetooth && mSerialPort != null) {
				mSerialPort.write(data, 100);	// timeout 100ms
			}
		} catch (Exception e) {
			Log.e(TAG, "SendMatchError Error", e);
		}
	}
	//------------------------------------------------------------------------
	// INSユニットへのコマンドを送信
	//------------------------------------------------------------------------
	private void SendCommand() {
		try {
			String msg = String.format(Locale.US,
				"TST=%d\r\n", fInsTest ? 1 : 0);
			byte[] data = msg.getBytes("US-ASCII");

			if (fBluetooth && BtSocket != null && BtSocket.isConnected()) {
				BtSocket.getOutputStream().write(data);
			} else if (!fBluetooth && mSerialPort != null) {
				mSerialPort.write(data, 100);	// timeout 100ms
			}
		} catch (Exception e) {
			Log.e(TAG, "SendCommand Error", e);
		}
	}
	//------------------------------------------------------------------------
	// TLS1.2 対応 OkHttpClient（最重要）
	//------------------------------------------------------------------------
	public static OkHttpClient enableTls12(OkHttpClient client) {
		try {
			SSLContext sc = SSLContext.getInstance("TLSv1.2");
			sc.init(null, null, null);

			ConnectionSpec cs = 
				new ConnectionSpec.Builder(ConnectionSpec.MODERN_TLS)
					.tlsVersions(TlsVersion.TLS_1_2)
					.build();

			return client.newBuilder()
				.sslSocketFactory(new Tls12SocketFactory(
					sc.getSocketFactory()), defaultTrustManager())
				.connectionSpecs(Collections.singletonList(cs))
				.build();
		} catch (Exception e) {
			return client;
		}
	}
	//------------------------------------------------------------------------
	// サーバーの証明書を検証
	//------------------------------------------------------------------------
	private static X509TrustManager defaultTrustManager() throws Exception {
		TrustManagerFactory tmf = TrustManagerFactory.getInstance(
			TrustManagerFactory.getDefaultAlgorithm());
		tmf.init((KeyStore) null);
		return (X509TrustManager) tmf.getTrustManagers()[0];
	}
	//------------------------------------------------------------------------
	// TLS1.2 ソケットラッパ
	//------------------------------------------------------------------------
	public static class Tls12SocketFactory extends SSLSocketFactory {
		private final SSLSocketFactory delegate;

		public Tls12SocketFactory(SSLSocketFactory base) {
			this.delegate = base;
		}

		@Override
		public Socket createSocket(Socket s, String host, int port,
			boolean autoClose) throws IOException {

			Socket socket = delegate.createSocket(s, host, port, autoClose);
			return patch(socket);
		}

		@Override
		public Socket createSocket() throws IOException {
			Socket socket = delegate.createSocket();
			return patch(socket);
		}

		private Socket patch(Socket socket) {
			if (socket instanceof SSLSocket) {
				((SSLSocket) socket).setEnabledProtocols(
					new String[]{"TLSv1.2"});
			}
			return socket;
		}

		// その他のメソッドは delegate を使う
		@Override public String[] getDefaultCipherSuites() {
			return delegate.getDefaultCipherSuites();
		}
		@Override public String[] getSupportedCipherSuites() {
			return delegate.getSupportedCipherSuites();
		}
		@Override public Socket createSocket(String host, int port)
			throws IOException {

			return patch(delegate.createSocket(host, port));
		}
		@Override public Socket createSocket(String host, int port,
			InetAddress localHost, int localPort) throws IOException {

			return patch(delegate.createSocket(
				host, port, localHost, localPort)); 
		}
		@Override public Socket createSocket(InetAddress host, int port)
			throws IOException {

			return patch(delegate.createSocket(host, port));
		}
		@Override public Socket createSocket(InetAddress address, int port,
			InetAddress localAddress, int localPort) throws IOException {

			return patch(delegate.createSocket(
				address, port, localAddress, localPort));
		}
	}
//****************************************************************************
// タイマー(100ms)
//
	//------------------------------------------------------------------------
	// タイマー割込み処理
	//------------------------------------------------------------------------
	private final Runnable TimerTask = new Runnable() {
		@Override
		public void run() {

			//----------------------------------------------------------------
			// 起動からしばらくの間の処理
			// NAVI本体GPSの方が早く立ち上がっていればそちらを使いたい。
			// そのため起動後しばらくはMockを禁止してNAVI本体GPSのFIXを待つ
			//
			// サービス開始かつ受信確定からの経過時間0.1s単位
			if (fExtGpsRxOk && TimeAfterRxFix < 10000) {
				TimeAfterRxFix++;
				if (TimeAfterRxFix == 1) {
//					ToastShow("■外付けGPSが確定しました");
				}
			}
			// 起動後しばらくは
			if (TimeAfterRxFix < POWERON_DELAY) {
				fMockForceDisable = true;		// Mockしない
			// 時間が来た時
			// すでに内部GPSが確定しているならあえてMockする必要はない
			} else if (TimeAfterRxFix == POWERON_DELAY) {
				if (!fIntGpsFix) {				// 内部GPSが未確定なら
					fMockForceDisable = false;	// 以後はMock可能とする
//					ToastShow("Mockレディ(NAVI本体GPSロスト)");
				}
			// 時間が経過した後
			} else {
				// 内部＆外部ともGPSが確定したか十分時間が経過(F/S)したら
				if (fMockForceDisable &&
						((fIntGpsFix && fExtGpsFix) ||
											TimeAfterRxFix >= 1800)) {
					fMockForceDisable = false;	// 以後はMock可能とする
//					ToastShow("Mockレディ(GPS確定または時間経過)");
				}
			}
			//----------------------------------------------------------------
			// スリープからの復帰を検出
			//----------------------------------------------------------------
			long now = System.currentTimeMillis();	// 今の時刻
			if (LastTime != 0L && now - LastTime > 30000L) {
				DebugToastShow("スリープ状態からの復帰");
				RestartCom();		// 通信再起動
				TimeoutDelay = 3;	// しばらくの期間はタイムアウト表示なし
				CloseLogFile();		// 念のためログファイルクローズ

				fScreenOff = false;
			}
			LastTime = now;

			//----------------------------------------------------------------
			// 外付けGPS受信タイムアウトチェック
			//----------------------------------------------------------------
			// 外付けGPS受信間隔カウンタインクリメント
			ExtRxTime = AddOnTime(true, ExtRxTime);
			// 受信タイムアウト
			if (ExtRxTime == 100) {		// 受信できずに時間が経過した
				ExtRxTime = 0;
				RestartCom();			// 通信再起動
				// USB利用か、BT利用かつBTオンなら
				if (!fBluetooth || (fBluetooth && fBluetoothEnabled)) {
					if (TimeoutDelay == 0) {
//						ToastShow("受信タイムアウト");
					}
				}
				if (TimeoutDelay > 0) {
					TimeoutDelay--;
				}
			}

			// 外付けGPS/内部GPS切り替え判断。結果はfExtGpsUseに反映
			JudgeExtIntGps();

			//----------------------------------------------------------------
			// 外付けGPS/本体GPS切り替え処理
			//----------------------------------------------------------------
			// 変化したら疑似プロバイダの状態を切り替える
			if (fExtGpsUse != fExtGpsUseZ) {

				if (fExtGpsUse) {	// 外付けGPS使用するなら
					// 音を出す
					// NaviFlyでは他のアプリの音が止まってしまう
					if (fMockSound) {
//						toneGenerator.startTone(ToneGenerator.TONE_PROP_NACK);
					}
//					ToastShow("■外付けGPSを使用します");
					// 全疑似プロバイダ開始
					AddMockProvider();
				} else {
					// 音を出す
					// NaviFlyでは他のアプリの音が止まってしまう
					if (fMockSound) {
//						toneGenerator.startTone(ToneGenerator.TONE_PROP_ACK);
					}
//					ToastShow("★ナビ本体のGPSを使用します");
					// 全疑似プロバイダ終了
					RemoveMockProvider();
				}
			}
			fExtGpsUseZ = fExtGpsUse;

			//----------------------------------------------------------------
			// ログリクエスト
			//----------------------------------------------------------------
			if (fLogging != fLoggingZ) {	// ログ要求が変化した？
				if (fLogging) {				// ログ開始要求
					OpenLogFile();			// ログファイルオープン
				} else {
					CloseLogFile();			// ログファイルクローズ
				}
			}
			fLoggingZ = fLogging;

			//----------------------------------------------------------------
			// 画面がオフになったら
			// ログファイルをクローズし、サービスを終了させる
			//----------------------------------------------------------------
			if (fScreenOff) {		// 画面のオフが発生したら
				// ログファイルクローズ
				CloseLogFile();
				fLogging = false;

				EndMsg = "画面オフ";
				stopSelf();			// サービス終了
			}

			// タイマー再開
			mTimerHandler.postDelayed(this, 100);
		}
	};
	//------------------------------------------------------------------------
	// 外付けGPS/内部GPS切り替え判断。結果はfExtGpsUseに反映
	//------------------------------------------------------------------------
	private void JudgeExtIntGps() {
		boolean fmock = true;
		// メインオンでMockイネイブルで外付けGPS受信していたら
		if (fMain && fMockEnable && fExtGpsRxOk) {
			// GPSロストによりINSしている場合にのみMockする場合
			if (fMockGpsIns) {
				fmock = (ExtSatNum <= 2);
			}
			fExtGpsUse = fmock;
		} else {	// メインオフなら
			fExtGpsUse = false;		// 強制的に内部GPS使用に
		}
		// Mock条件にチェックが入っていて強制的に内部GPS使用にするなら
		if (fMockGpsIns && fMockForceDisable) {
			fExtGpsUse = false;
		}
	}
//****************************************************************************
// ファイル操作
//
	//------------------------------------------------------------------------
	// ログファイル名を得る
	//------------------------------------------------------------------------
	private void MakeLogFileName() {
		Calendar now = Calendar.getInstance();	// カレンダー取得
		@SuppressLint("SimpleDateFormat")
		SimpleDateFormat sdf =
				new SimpleDateFormat("yyyy_MMdd_HHmmss");
		if (DataType == 1) {	// NMEAフォーマットなら
			sLogFile = "NMEA" + sdf.format(now.getTime()) + ".txt";
		} else {
			sLogFile = "Log" + sdf.format(now.getTime()) + ".txt";
		}
		sMp4File = sLogFile.replace(".txt", ".mp4");
		sLogFilePathName = sDocDir + "/" + sLogFile;
		sMp4FilePathName = sDocDir + "/" + sMp4File;
		return;
	}
	//------------------------------------------------------------------------
	// ログ＆キャプチャファイルオープン
	//------------------------------------------------------------------------
	private void OpenLogFile() {
		// ストレージが書き込みできるかチェック
		if (isExternalStorageWritable()) {

			DocDir.mkdir();	// docディレクトリがなければ作成
			if (!DocDir.exists()) {
				ToastShow("ドキュメントフォルダが作成できません");
				return;
			}

			CloseLogFile();		// 念のため今開いていたら閉じる
			MakeLogFileName();	// パスとファイル名を作成
			LogFile = new File(sLogFilePathName);	// ログファイル
			Mp4File = new File(sMp4FilePathName);	// mp4ファイル

			try {
				if (LogFile.exists()) {	// ファイルが存在していれば
					LogFile.delete();	// いったん削除
				}
				bufferedWriter = new BufferedWriter(
					new OutputStreamWriter(
						new FileOutputStream(LogFile, true), sEncode));

				if (Mp4File.exists()) {	// ファイルが存在していれば
					Mp4File.delete();	// いったん削除
				}
				StartRec();				// キャプチャ開始
			} catch (Exception e) {
				ToastShow("ストレージへの書き込みができません");
				bufferedWriter = null;
				LogFile = null;
				return;
			}
			LogLine = 0;
			if (fCapture) {
				ToastShow(sLogFile + " 記録開始\n" + sMp4File + " 記録開始");
			} else {
				ToastShow(sLogFile + " 記録開始");
			}
		} else {
			ToastShow("ストレージへの書き込み許可がありません");
			bufferedWriter = null;
			LogFile = null;
		}
	}
	//------------------------------------------------------------------------
	// ログ＆キャプチャファイルクローズ
	//------------------------------------------------------------------------
	private void CloseLogFile() {
		if (bufferedWriter != null) {
			try {
				bufferedWriter.close();	// ログファイルクローズ
				StopRec();				// キャプチャ終了
				if (fCapture) {
					ToastShow(sLogFile + " 記録終了\n" +
								sMp4File + " 記録終了");
				} else {
					ToastShow(sLogFile + " 記録終了");
				}
			} catch (Exception e) {
				ToastShow("ファイルがクローズできません");
			}
		}
		bufferedWriter = null;
		LogFile = null;
	}
	//------------------------------------------------------------------------
	// ログファイル書き込み
	//------------------------------------------------------------------------
	private void WriteLogFile(String sdata) {
		// ファイルがオープンされていないなら何もしない
		if (bufferedWriter == null || LogFile == null || !fLogging) { 
			return;
		}

		if (DataType == 2) {	// ログフォーマットなら
			// マップマッチデータを追加
			String match = String.format(Locale.US, ",%d,%d,%f,%f",
				(long)(MatchLon * 10000000.0d),
				(long)(MatchLat * 10000000.0d),
				MatchDir,
				mydebug);
			sdata += match;
		}

		// ストレージが書き込みできるかチェック
		if (isExternalStorageWritable()) {
			try {
				bufferedWriter.write(sdata);	// データ行を書き込む
				bufferedWriter.write("\r\n");	// 改行を書き込む
				LogLine++;						// 書き込んだ行数を+1
				// ログ行がいっぱいになたら
				if (LogLine > 30000) {	// 最大行数に達した？
					CloseLogFile();		// いったんログファイルクローズして
					OpenLogFile();		// 新規にオープン
				}
			} catch (Exception e) {
				ToastShow("データ書き込みエラー");
				bufferedWriter = null;
				LogFile = null;
			}
		} else {
			ToastShow("ストレージへの書き込み許可がありません");
			bufferedWriter = null;
			LogFile = null;
		}
	}
	//------------------------------------------------------------------------
	// ストレージが書き込みできるかのチェック
	//------------------------------------------------------------------------
	private boolean isExternalStorageWritable() {
		String state = Environment.getExternalStorageState();

		if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.R) {
			return (Environment.MEDIA_MOUNTED.equals(state) &&
					Environment.isExternalStorageManager());
		}
		return (Environment.MEDIA_MOUNTED.equals(state) &&
					ActivityCompat.checkSelfPermission(this,
						Manifest.permission.WRITE_EXTERNAL_STORAGE) ==
								PackageManager.PERMISSION_GRANTED);
	}
//****************************************************************************
// 画面録画
//
	//------------------------------------------------------------------------
	// 録画開始
	//------------------------------------------------------------------------
	@SuppressWarnings("deprecation")
	private void StartRec() {
		StopRec();
		if (mResultData != null) {
			mpManager = (MediaProjectionManager)
				getSystemService(Context.MEDIA_PROJECTION_SERVICE);

			mProjection =
				mpManager.getMediaProjection(Activity.RESULT_OK, mResultData);

			if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.S) {
				mMediaRecorder = new MediaRecorder(this);
			} else {
				mMediaRecorder = new MediaRecorder();
			}
			mMediaRecorder.setVideoSource(MediaRecorder.VideoSource.SURFACE);
			mMediaRecorder.setOutputFormat(MediaRecorder.OutputFormat.MPEG_4);
			mMediaRecorder.setVideoEncoder(MediaRecorder.VideoEncoder.H264);
			mMediaRecorder.setVideoEncodingBitRate(1280000);
			mMediaRecorder.setCaptureRate(10);		// 描画が10回/秒なので
			mMediaRecorder.setVideoFrameRate(30);	// 3倍速で再生
			mMediaRecorder.setVideoSize(
				(mDisplayWidth / 16) * 16,
				(mDisplayHeight / 16) * 16);
			mMediaRecorder.setOutputFile(sMp4FilePathName);
			try {
				mMediaRecorder.prepare();
			} catch (Exception e) {
				Log.e("REC", "prepare failed", e);
			}
			try {
				Surface surface = mMediaRecorder.getSurface();

				mVirtualDisplay = mProjection.createVirtualDisplay(
					"recode",
					mDisplayWidth,
					mDisplayHeight,
					mScreenDensity,
					DisplayManager.VIRTUAL_DISPLAY_FLAG_AUTO_MIRROR,
					surface,
					null,
					null);
				// 少し待つ
				Thread.sleep(100);
				// 開始
				mMediaRecorder.start();
			} catch (Exception e) {
				Log.e("REC", "surface failed", e);
				StopRec();
			}
		}
	}

	//------------------------------------------------------------------------
	// 録画停止
	//------------------------------------------------------------------------
	private void StopRec() {
		if (mMediaRecorder != null) {
			try {
				mMediaRecorder.stop();
			} catch (Exception e) {
			}
		}
		if (mMediaRecorder != null) {
			mMediaRecorder.reset();
			mMediaRecorder.release();
			mMediaRecorder = null;
		}
		if (mVirtualDisplay != null) {
			mVirtualDisplay.release();
			mVirtualDisplay = null;
		}
		if (mProjection != null) {
			mProjection.stop();
			mProjection = null;
		}
	}
//****************************************************************************
// 画面表示
//
	//------------------------------------------------------------------------
	//	toast出力
	//------------------------------------------------------------------------
	private void ToastShow0(String str) {
		Toast tst;
		tst = Toast.makeText(this, str, Toast.LENGTH_LONG);
		// 画面の中央に表示
		//tst.setGravity(Gravity.CENTER, 0, 0);
		tst.show();
	}
	//------------------------------------------------------------------------
	// 別スレッドでtoast出力
	// https://qiita.com/glayash/items/c75a670e2c11938a2bdc
	//------------------------------------------------------------------------
	private void ToastShow(String str) {
		new ToastThread(this, str).start();
	}
	private static Toast t;
	private static class ToastThread extends Thread {
		final private Context context;
		final private CharSequence message;
		private ToastThread(Context context, CharSequence message){
			this.context = context.getApplicationContext();
			this.message = message;
		}
		@Override
		public void run() {
			Looper.prepare();
			t = Toast.makeText(context, message, Toast.LENGTH_LONG);
			t.show();
			Looper.loop();
		}
	}
	//------------------------------------------------------------------------
	//	デバッグビルド時のみtoast出力
	//------------------------------------------------------------------------
	private void DebugToastShow(String str) {
		if (BuildConfig.DEBUG) {
			ToastShow(str);
		}
	}
//****************************************************************************
// Misc
//
	//------------------------------------------------------------------------
	// カウンタインクリメント
	//------------------------------------------------------------------------
	private int AddOnTime(boolean f, int count) {
		if (f) {
			if (count < 30000) {
				count++;
			}
		} else {
			count = 0;
		}
		return count;
	}
	//------------------------------------------------------------------------
	// カウンタデクリメント
	//------------------------------------------------------------------------
	private int DecNonZero(int count) {
		if (count > 0) {
			count--;
		}
		return count;
	}
}
