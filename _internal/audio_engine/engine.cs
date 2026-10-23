// Audio engine for Lettuce Player. Compiled at start-up by the PowerShell host (Add-Type, C# 5) next to the NAudio DLLs.
// Chain: MediaFoundationReader (decodes mp3/m4a/mp4/wav/wma and http streams) -> 3-band EQ -> volume + fades -> speakers.
using System;
using System.Collections.Concurrent;
using System.Globalization;
using System.IO;
using System.Text;
using System.Threading;
using NAudio.Wave;
using NAudio.Wave.SampleProviders;

namespace Lettuce
{
    // Reads command lines from stdin on a background thread (Console.In reads would block the host's loop)
    public class Rd
    {
        public static ConcurrentQueue<string> Q = new ConcurrentQueue<string>();
        public static void Start()
        {
            Thread t = new Thread(delegate ()
            {
                string line;
                while ((line = Console.In.ReadLine()) != null) Q.Enqueue(line);
                Q.Enqueue("quit");
            });
            t.IsBackground = true;
            t.Start();
        }
    }

    // One second-order filter section (RBJ audio EQ cookbook), direct form I
    public class Biquad
    {
        double b0 = 1, b1, b2, a1, a2, x1, x2, y1, y2;

        public void Set(double nb0, double nb1, double nb2, double na0, double na1, double na2)
        {
            b0 = nb0 / na0; b1 = nb1 / na0; b2 = nb2 / na0; a1 = na1 / na0; a2 = na2 / na0;
        }

        public float Process(float x)
        {
            double y = b0 * x + b1 * x1 + b2 * x2 - a1 * y1 - a2 * y2;
            x2 = x1; x1 = x; y2 = y1; y1 = y;
            return (float)y;
        }

        public void LowShelf(double fs, double f0, double gainDb)
        {
            double A = Math.Pow(10, gainDb / 40), w = 2 * Math.PI * f0 / fs, c = Math.Cos(w), s = Math.Sin(w);
            double alpha = s / 2 * Math.Sqrt((A + 1 / A) * (1 / 1.0 - 1) + 2), k = 2 * Math.Sqrt(A) * alpha;
            Set(A * ((A + 1) - (A - 1) * c + k), 2 * A * ((A - 1) - (A + 1) * c), A * ((A + 1) - (A - 1) * c - k),
                (A + 1) + (A - 1) * c + k, -2 * ((A - 1) + (A + 1) * c), (A + 1) + (A - 1) * c - k);
        }

        public void HighShelf(double fs, double f0, double gainDb)
        {
            double A = Math.Pow(10, gainDb / 40), w = 2 * Math.PI * f0 / fs, c = Math.Cos(w), s = Math.Sin(w);
            double alpha = s / 2 * Math.Sqrt((A + 1 / A) * (1 / 1.0 - 1) + 2), k = 2 * Math.Sqrt(A) * alpha;
            Set(A * ((A + 1) + (A - 1) * c + k), -2 * A * ((A - 1) + (A + 1) * c), A * ((A + 1) + (A - 1) * c - k),
                (A + 1) - (A - 1) * c + k, 2 * ((A - 1) - (A + 1) * c), (A + 1) - (A - 1) * c - k);
        }

        public void Peaking(double fs, double f0, double gainDb, double q)
        {
            double A = Math.Pow(10, gainDb / 40), w = 2 * Math.PI * f0 / fs, c = Math.Cos(w);
            double alpha = Math.Sin(w) / (2 * q);
            Set(1 + alpha * A, -2 * c, 1 - alpha * A, 1 + alpha / A, -2 * c, 1 - alpha / A);
        }
    }

    // Bass (low shelf 150 Hz), mid (peak 1 kHz), treble (high shelf 5 kHz), each -12..+12 dB
    public class EqProvider : ISampleProvider
    {
        readonly ISampleProvider source;
        readonly int channels;
        readonly Biquad[][] bands; // [band][channel]
        readonly object gate = new object();
        bool active;
        float headroom = 1f;

        public EqProvider(ISampleProvider source)
        {
            this.source = source;
            channels = source.WaveFormat.Channels;
            bands = new Biquad[3][];
            for (int b = 0; b < 3; b++)
            {
                bands[b] = new Biquad[channels];
                for (int c = 0; c < channels; c++) bands[b][c] = new Biquad();
            }
        }

        public WaveFormat WaveFormat { get { return source.WaveFormat; } }

        public void SetGains(double bassDb, double midDb, double trebleDb)
        {
            double fs = source.WaveFormat.SampleRate;
            lock (gate)
            {
                for (int c = 0; c < channels; c++)
                {
                    bands[0][c].LowShelf(fs, 150, bassDb);
                    bands[1][c].Peaking(fs, 1000, midDb, 0.7);
                    bands[2][c].HighShelf(fs, 5000, trebleDb);
                }
                active = Math.Abs(bassDb) > 0.05 || Math.Abs(midDb) > 0.05 || Math.Abs(trebleDb) > 0.05;
                double boost = Math.Max(0, Math.Max(bassDb, Math.Max(midDb, trebleDb)));
                headroom = (float)Math.Pow(10, -0.4 * boost / 20.0); // a little headroom for boosts, the soft clip below catches the rest
            }
        }

        static float SoftClip(float x)
        {
            float a = Math.Abs(x);
            if (a <= 0.9f) return x;
            float y = 0.9f + 0.1f * (float)Math.Tanh((a - 0.9f) / 0.1f);
            return x < 0 ? -y : y;
        }

        public int Read(float[] buffer, int offset, int count)
        {
            int n = source.Read(buffer, offset, count);
            lock (gate)
            {
                if (!active) return n;
                for (int i = 0; i + channels <= n; i += channels)
                {
                    for (int c = 0; c < channels; c++)
                    {
                        float x = buffer[offset + i + c];
                        x = bands[0][c].Process(x);
                        x = bands[1][c].Process(x);
                        x = bands[2][c].Process(x);
                        buffer[offset + i + c] = SoftClip(x * headroom);
                    }
                }
            }
            return n;
        }
    }

    // Decodes the first moments of a track in one go before the sound starts, so later reads from
    // the sound card are instant. Without it, slow start-up reads (opening the file, JIT) stutter right where the fade-in is.
    public class Preroll : ISampleProvider
    {
        readonly ISampleProvider source;
        readonly float[] buf;
        readonly object gate = new object();
        int have, pos;
        bool filled;

        public Preroll(ISampleProvider source, double seconds)
        {
            this.source = source;
            buf = new float[(int)(seconds * source.WaveFormat.SampleRate) * source.WaveFormat.Channels];
        }

        // Done on the first read, so every read of the decoder happens on the audio thread (Media Foundation readers
        // stop returning data when they are read from two different threads)
        void Fill()
        {
            filled = true;
            int got = 0;
            while (got < buf.Length)
            {
                int n = source.Read(buf, got, buf.Length - got);
                if (n <= 0) break;
                got += n;
            }
            have = got;
        }

        public WaveFormat WaveFormat { get { return source.WaveFormat; } }

        public int Read(float[] buffer, int offset, int count)
        {
            lock (gate)
            {
                if (!filled) Fill();
                int n = 0;                if (pos < have)
                {
                    n = Math.Min(count, have - pos);
                    for (int i = 0; i < n; i++) buffer[offset + i] = buf[pos + i]; // not Array.Copy: some outputs hand over a reinterpreted array
                    pos += n;
                }
                if (n < count) n += source.Read(buffer, offset + n, count - n);
                return n;
            }
        }

        // Moves the underlying reader and throws away the stale buffered audio, as one step the audio thread can't interleave with
        public void Reposition(Action move)
        {
            lock (gate)
            {
                if (!filled) { filled = true; have = 0; }
                move();
                pos = have;
            }
        }
    }

    // Volume, mute, fade in/out and pause fades. Every change is smoothed per sample, so nothing ever clicks or steps.
    public class Fader : ISampleProvider
    {
        readonly ISampleProvider source;
        readonly int channels, rate;
        public volatile float Volume = 0.8f;
        public volatile bool Muted;
        float volumeNow, fade;          // fade: 0 = silent, 1 = full
        float fadeTarget = 1f, fadeStep;
        long frames;                     // frames played since the start of the track
        long totalFrames;                // 0 for live streams
        long tailFrames;                 // fade-out length at the end of a track
        // 14-band spectrum of what is being played, for the on-screen visualizer (a 2048-point FFT grouped into pitch bands)
        const int FftSize = 2048;
        readonly double[] re = new double[FftSize], im = new double[FftSize];
        readonly float[] levels = new float[14];
        int lastRead;
        long leadFrames;                 // silence before the track starts, so the fade-in begins once the sound card is running

        public Fader(ISampleProvider source, long totalFrames, double fadeIn, double fadeOut)
        {
            this.source = source;
            channels = source.WaveFormat.Channels;
            rate = source.WaveFormat.SampleRate;
            this.totalFrames = totalFrames;
            double fadeSeconds = fadeIn;
            if (totalFrames > 0) fadeSeconds = Math.Min(fadeIn, totalFrames / (double)rate / 3.0); // never longer than a third of the song
            SetTail(fadeOut);
            leadFrames = (long)(0.12 * rate);
            fade = 0f;
            FadeTo(1f, (float)Math.Max(fadeSeconds, 0));
            volumeNow = Muted ? 0f : Volume;
        }

        public WaveFormat WaveFormat { get { return source.WaveFormat; } }
        public long Frames { get { return frames; } }
        public long TotalFrames { get { return totalFrames; } }
        public int Rate { get { return rate; } }

        public void FadeTo(float target, float seconds)
        {
            fadeTarget = target;
            fadeStep = Math.Max(1e-6f, 1f / Math.Max(seconds * rate, 1f));
        }

        // The output asks for small blocks, so the latest FftSize samples are kept in a ring and analysed every half window
        readonly double[] ring = new double[FftSize];
        int ringPos, sinceAnalysis;

        void Analyze(float[] buffer, int offset, int n)
        {
            int frames = n / channels;
            for (int i = 0; i < frames; i++)
            {
                double x = 0;
                for (int c = 0; c < channels; c++) x += buffer[offset + i * channels + c];
                ring[ringPos] = x / channels;
                ringPos = (ringPos + 1) % FftSize;
            }
            sinceAnalysis += frames;
            lastRead = Environment.TickCount;
            if (sinceAnalysis < FftSize / 2) return;
            sinceAnalysis = 0;
            for (int i = 0; i < FftSize; i++)
            {
                re[i] = ring[(ringPos + i) % FftSize] * (0.5 - 0.5 * Math.Cos(2 * Math.PI * i / FftSize)); // oldest first, Hann window
                im[i] = 0;
            }
            for (int i = 1, j = 0; i < FftSize; i++) // bit-reversal
            {
                int bit = FftSize >> 1;
                for (; (j & bit) != 0; bit >>= 1) j ^= bit;
                j ^= bit;
                if (i < j) { double t = re[i]; re[i] = re[j]; re[j] = t; t = im[i]; im[i] = im[j]; im[j] = t; }
            }
            for (int len = 2; len <= FftSize; len <<= 1)
            {
                double ang = -2 * Math.PI / len, wr = Math.Cos(ang), wi = Math.Sin(ang);
                for (int i = 0; i < FftSize; i += len)
                {
                    double cr = 1, ci = 0;
                    for (int k = 0; k < len / 2; k++)
                    {
                        int u = i + k, v = i + k + len / 2;
                        double xr = re[v] * cr - im[v] * ci, xi = re[v] * ci + im[v] * cr;
                        re[v] = re[u] - xr; im[v] = im[u] - xi; re[u] += xr; im[u] += xi;
                        double nr = cr * wr - ci * wi; ci = cr * wi + ci * wr; cr = nr;
                    }
                }
            }
            double binHz = (double)rate / FftSize;
            int bands = levels.Length;
            for (int b = 0; b < bands; b++)
            {
                double lo = 40 * Math.Pow(16000.0 / 40, (double)b / bands), hi = 40 * Math.Pow(16000.0 / 40, (double)(b + 1) / bands);
                int first = (int)(lo / binHz), last = Math.Max(first, (int)(hi / binHz) - 1);
                last = Math.Min(last, FftSize / 2 - 1);
                double peak = 0;
                for (int k = first; k <= last; k++) peak = Math.Max(peak, Math.Sqrt(re[k] * re[k] + im[k] * im[k]));
                double amp = peak / (FftSize / 4.0); // a full-scale sine reads 1.0 after the window
                double mid = Math.Sqrt(lo * hi);
                double db = amp > 1e-6 ? 20 * Math.Log10(amp) + 2.0 * Math.Log(mid / 100.0, 2) : -100; // highs are naturally quieter, so lift them a little
                levels[b] = (float)Math.Max(0, Math.Min(1, (db + 54) / 46));
            }
        }

        public float[] CurrentLevels()
        {
            if (Environment.TickCount - lastRead > 300) return new float[14]; // nothing is being read: paused or stopped
            return (float[])levels.Clone();
        }

        public void SetTail(double seconds)
        {
            if (totalFrames > 0) seconds = Math.Min(seconds, totalFrames / (double)rate / 3.0);
            tailFrames = (long)(Math.Max(seconds, 0) * rate);
        }

        public void SetFrames(long position) { frames = position; }

        public int Read(float[] buffer, int offset, int count)
        {
            if (leadFrames > 0) // the fade and the track both wait: nothing is consumed while the output warms up
            {
                for (int i = 0; i < count; i++) buffer[offset + i] = 0f; // not Array.Clear, for the same reason
                leadFrames -= count / channels;
                return count;
            }
            int n = source.Read(buffer, offset, count);
            Analyze(buffer, offset, n);
            float volumeGoal = Muted ? 0f : Volume;
            for (int i = 0; i + channels <= n; i += channels)
            {
                if (fade < fadeTarget) fade = Math.Min(fadeTarget, fade + fadeStep);
                else if (fade > fadeTarget) fade = Math.Max(fadeTarget, fade - fadeStep);
                volumeNow += (volumeGoal - volumeNow) * 0.002f;
                float tail = 1f;
                if (totalFrames > 0)
                {
                    long remaining = totalFrames - frames;
                    if (remaining < tailFrames) tail = remaining <= 0 ? 0f : remaining / (float)tailFrames;
                }
                float gain = volumeNow * fade * fade * tail * tail; // squared: closer to how loudness is perceived
                for (int c = 0; c < channels; c++) buffer[offset + i + c] *= gain;
                frames++;
            }
            return n;
        }
    }

    public class Engine
    {
        MediaFoundationReader reader;
        IWavePlayer output;
        const int OutputLatencyMs = 60; // how much audio the output holds ahead; also how long a stopped song can still be heard
        EqProvider eq;
        Fader fader;
        Preroll preroll;
        Timer pauseTimer;
        bool stopping;
        float volume = 0.8f;
        bool muted;
        double bass, mid, treble;
        double fadeInSeconds = 1.5, fadeOutSeconds = 1.5;

        public volatile bool EndedFlag;
        public string LastError = ""; // why the output stopped by itself, when it did so because of an error
        public string CurrentId = "";
        public bool Active { get { return output != null; } }
        public bool Paused;

        public double Position
        {
            get
            {
                Fader f = fader;
                return f == null ? 0 : f.Frames / (double)f.Rate;
            }
        }

        public double Duration
        {
            get
            {
                Fader f = fader;
                return f == null || f.TotalFrames <= 0 ? 0 : f.TotalFrames / (double)f.Rate;
            }
        }

        public void Play(string id, string uri)
        {
            StopSmooth();
            CurrentId = id;
            EndedFlag = false;
            MediaFoundationReader r = new MediaFoundationReader(uri);
            long total = 0;
            if (r.Length > 0 && r.TotalTime.TotalSeconds > 0.2 && r.TotalTime.TotalHours < 12)
                total = r.Length / r.WaveFormat.BlockAlign;
            ISampleProvider samples = r.ToSampleProvider();
            Preroll p = new Preroll(samples, total > 0 ? 1.0 : 0.5);
            EqProvider e = new EqProvider(p);
            e.SetGains(bass, mid, treble);
            Fader f = new Fader(e, total, fadeInSeconds, fadeOutSeconds);
            f.Volume = volume;
            f.Muted = muted;
            // WASAPI shared mode talks to the audio engine directly: far less queued audio than the old WinMM output
            IWavePlayer o = new NAudio.Wave.WasapiOut(NAudio.CoreAudioApi.AudioClientShareMode.Shared, true, OutputLatencyMs);
            o.PlaybackStopped += delegate (object s, StoppedEventArgs a)
            {
                if (a.Exception != null) LastError = a.Exception.ToString();
                if (!stopping && output == o) EndedFlag = true;
            };
            o.Init(new SampleToWaveProvider(f));
            reader = r; eq = e; fader = f; preroll = p; output = o;
            Paused = false;
            o.Play();
        }

        // Plays a moment of silence through the whole chain (decoder, EQ, fader, sound card) so the JIT and Media Foundation
        // start-up costs are paid now instead of stuttering the first real track
        public void Warm()
        {
            string path = Path.Combine(Path.GetTempPath(), "lettuce_warm.wav");
            try
            {
                using (WaveFileWriter w = new WaveFileWriter(path, new WaveFormat(44100, 16, 2)))
                    w.Write(new byte[44100 * 4], 0, 44100 * 4);
                Play("warm", new Uri(path).AbsoluteUri);
                Thread.Sleep(350);
            }
            finally
            {
                Stop();
                EndedFlag = false;
                try { File.Delete(path); } catch (Exception) { }
            }
        }

        public string LevelsText()
        {
            Fader f = fader;
            float[] l = f == null ? new float[14] : f.CurrentLevels();
            StringBuilder sb = new StringBuilder();
            for (int i = 0; i < l.Length; i++) sb.Append(i > 0 ? " " : "").Append(l[i].ToString("0.00", CultureInfo.InvariantCulture));
            return sb.ToString();
        }

        // Stops with a short fade so the old song doesn't end in a click or a sharp cut. The output holds a little audio
        // ahead (OutputLatencyMs), so the song is only stopped once the faded audio has actually been heard.
        public void StopSmooth()
        {
            Fader f = fader;
            if (output != null && f != null && !Paused)
            {
                f.FadeTo(0f, 0.12f);
                Thread.Sleep(120 + OutputLatencyMs + 20);
            }
            Stop();
        }

        public void Stop()
        {
            stopping = true;
            if (pauseTimer != null) { pauseTimer.Dispose(); pauseTimer = null; }
            if (output != null) { try { output.Stop(); } catch (Exception) { } output.Dispose(); output = null; }
            if (reader != null) { reader.Dispose(); reader = null; }
            fader = null; eq = null; preroll = null; Paused = false;
            stopping = false;
        }

        public void Pause()
        {
            if (output == null || Paused) return;
            Paused = true;
            fader.FadeTo(0f, 0.4f);
            IWavePlayer o = output;
            pauseTimer = new Timer(delegate (object state) { if (Paused && output == o) o.Pause(); }, null, 430, Timeout.Infinite);
        }

        public void Resume()
        {
            if (output == null || !Paused) return;
            Paused = false;
            if (pauseTimer != null) { pauseTimer.Dispose(); pauseTimer = null; }
            output.Play();
            fader.FadeTo(1f, 0.4f);
        }

        public void Seek(double seconds)
        {
            if (reader == null || fader.TotalFrames <= 0) return; // live streams can't seek
            seconds = Math.Max(0, Math.Min(seconds, Duration - 0.5));
            MediaFoundationReader r = reader;
            preroll.Reposition(delegate () { r.CurrentTime = TimeSpan.FromSeconds(seconds); });
            fader.SetFrames((long)(seconds * fader.Rate));
        }

        public void SetVolume(double v)
        {
            volume = (float)Math.Max(0, Math.Min(1, v));
            if (fader != null) fader.Volume = volume;
        }

        public void SetMuted(bool m)
        {
            muted = m;
            if (fader != null) fader.Muted = m;
        }

        // Fade lengths in seconds: the fade-in applies to the next track, the fade-out also to the one that's playing
        public void SetFades(double inSeconds, double outSeconds)
        {
            fadeInSeconds = Math.Max(inSeconds, 0);
            fadeOutSeconds = Math.Max(outSeconds, 0);
            Fader f = fader;
            if (f != null) f.SetTail(fadeOutSeconds);
        }

        public void SetEq(double bassDb, double midDb, double trebleDb)
        {
            bass = bassDb; mid = midDb; treble = trebleDb;
            if (eq != null) eq.SetGains(bass, mid, treble);
        }
    }
}
