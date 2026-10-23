// Windows' media controls (the "now playing" panel by the volume flyout). Registering there is what makes Bluetooth
// earbuds work properly: Windows sends their play / pause / next / previous presses to the registered player, and tells
// the earbuds whether it is playing, so a press sends the right one (AirPods send "play" and "pause", not a toggle).
//
// It is compiled ahead of time into smtc.dll, because PowerShell's Add-Type can't read Windows' .winmd files. To rebuild
// it after a change, run in this folder:
//   set NET=%windir%\Microsoft.NET\Framework64\v4.0.30319
//   %NET%\csc.exe -nologo -target:library -out:smtc.dll -r:%windir%\System32\WinMetadata\Windows.Media.winmd
//     -r:%windir%\System32\WinMetadata\Windows.Foundation.winmd -r:%NET%\System.Runtime.WindowsRuntime.dll
//     -r:%NET%\System.Runtime.dll -r:%NET%\System.Runtime.InteropServices.WindowsRuntime.dll smtc.cs
using System.Collections.Concurrent;
using Windows.Foundation;
using Windows.Media;
using Windows.Media.Playback;

namespace Lettuce {
    public static class Smtc {
        static MediaPlayer player; // only lends its media controls: it never plays anything itself
        static SystemMediaTransportControls controls;
        static TypedEventHandler<SystemMediaTransportControls, SystemMediaTransportControlsButtonPressedEventArgs> handler; // kept alive with the controls
        public static ConcurrentQueue<string> Pressed = new ConcurrentQueue<string>(); // "Play", "Pause", "Next", "Previous", "Stop"

        public static void Start() {
            player = new MediaPlayer();
            player.CommandManager.IsEnabled = false; // the buttons are handled here, not by the unused MediaPlayer
            controls = player.SystemMediaTransportControls;
            controls.IsEnabled = true;
            controls.IsPlayEnabled = true;
            controls.IsPauseEnabled = true;
            controls.IsNextEnabled = true;
            controls.IsPreviousEnabled = true;
            controls.IsStopEnabled = true;
            handler = (sender, e) => Pressed.Enqueue(e.Button.ToString()); // on a Windows thread: just queued
            controls.ButtonPressed += handler;
            Show("stopped", "");
        }

        public static void Show(string status, string title) {
            controls.PlaybackStatus = status == "playing" ? MediaPlaybackStatus.Playing
                : status == "paused" ? MediaPlaybackStatus.Paused : MediaPlaybackStatus.Stopped;
            var display = controls.DisplayUpdater;
            display.Type = MediaPlaybackType.Music;
            display.MusicProperties.Title = title;
            display.Update();
        }
    }
}
