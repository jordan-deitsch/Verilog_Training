import numpy as np
import pandas as pd
import argparse
import sys

import tkinter as tk
from tkinter import filedialog
import matplotlib
matplotlib.use("TkAgg")   # or "Qt5Agg" if you have PyQt5 installed
import matplotlib.pyplot as plt

def peak_bounds(arr, index=-1):
    # Find index of maximum value
    if index < 0:
        peak_idx = np.argmax(arr)
    else:
        peak_idx = index

    # Walk left until the values start increasing
    left_idx = peak_idx
    while left_idx > 0 and arr[left_idx - 1] <= arr[left_idx]:
        left_idx -= 1

    # Walk right until the values start increasing
    right_idx = peak_idx
    while right_idx < len(arr) - 1 and arr[right_idx + 1] <= arr[right_idx]:
        right_idx += 1

    return peak_idx, left_idx, right_idx

sampling_rate = 125000000    # in Hz (samples per second). Adjust for your dataset

# Hide the root Tk window
root = tk.Tk()
root.withdraw()

# Open file explorer
file_path = filedialog.askopenfilename(
    title="Select a CSV file",
    filetypes=[("CSV files", "*.csv"), ("All files", "*.*")]
)

if file_path:
    print("Selected file:", file_path)
else:
    print("No file selected")
    print("Exiting now...")
    sys.exit()

# Set up argument parser
parser = argparse.ArgumentParser(description="Read a file and perform FFT")
parser.add_argument('-c', '--channel', type=int, default=1, help="Select channel to analyze in frame data")
args = parser.parse_args()
channel = args.channel

if (channel < 1) or (channel > 4):
    print("Invalid channel entry, default to 1")

# === Load Data ===
# Read each row to find the desired channel, drop first 2 entries, and convert to numpy array
data_frame = pd.read_csv(file_path, header=None)
row_data = data_frame.iloc[0].values
signal = row_data[2:-1].astype(float)  # skip first 2 entries

for row_id in range(0, len(data_frame)):
    if data_frame.iloc[row_id, 0] == channel:
        row_data = data_frame.iloc[row_id].values
        signal = row_data[2:-1].astype(float)  # skip first 2 entries
        break

# === Apply Hann window ===
n = len(signal)
window = np.hanning(n)
windowed_signal = signal * window

# === FFT ===
t = np.arange(n) / sampling_rate
fft_vals = np.fft.fft(windowed_signal)
fft_freqs = np.fft.fftfreq(n, d=1/sampling_rate)

# Take only positive frequencies
pos_mask = fft_freqs >= 0
fft_freqs = fft_freqs[pos_mask] / 1000000
fft_power = np.abs(fft_vals[pos_mask]) / n
fft_db = 20 * np.log10(fft_power + 1e-12)  # add small number to avoid log(0)

# === SINAD & ENOB calculation ===
power_spectrum = fft_power**2
noise_spectrum = np.copy(power_spectrum)

# Find peaks (ignoring DC at index 0)
peak_index, peak_low, peak_high = peak_bounds(power_spectrum)
for i in range(peak_low, peak_high+1):
    noise_spectrum[i] = 0

dc_index, dc_low, dc_high = peak_bounds(noise_spectrum, 0)
for i in range(0, dc_high + 1):
    noise_spectrum[i] = 0

P_signal = np.sum(power_spectrum[peak_low:peak_high])
P_noise = np.sum(noise_spectrum)

SINAD = 10 * np.log10(P_signal / P_noise)
ENOB = (SINAD - 1.76) / 6.02

print(f"SINAD = {SINAD:.2f} dB")
print(f"ENOB  = {ENOB:.2f} bits")

# Find next peak (harmonic)
harm_index, harm_low, harm_high = peak_bounds(noise_spectrum)
peak_indices = np.array([peak_index, harm_index])
peak_freqs = fft_freqs[peak_indices]
peak_amps = fft_db[peak_indices]

# === Plot Results ===
plt.figure(figsize=(12,6))

# Time-domain signal
plt.subplot(2,1,1)
plt.plot(t, signal, label="Original")
plt.plot(t, windowed_signal, label="Windowed", alpha=0.7)
plt.ylim(-35000, 35000)
plt.xlim(t[0], t[-1])
plt.axhline(y=-32768, color='r', linestyle='--')
plt.axhline(y=32768, color='r', linestyle='--')

plt.title("Time-Domain Signal (Hann Window Applied)")
plt.xlabel("Time [s]")
plt.ylabel("Amplitude")
plt.legend()

# Frequency-domain signal
plt.subplot(2,1,2)
plt.plot(fft_freqs, fft_db, label="FFT Spectrum")
plt.ylim(-80, fft_db[peak_index] + 10)
plt.xlim(fft_freqs[0], fft_freqs[-1])

plt.scatter(peak_freqs, peak_amps, color="red", zorder=5, label="Top Peaks")
for f, a in zip(peak_freqs, peak_amps):
    plt.annotate(f"{f:.1f} MHz, {a:.2f} dB", (f, a), textcoords="offset points", xytext=(0,10), ha="center")

plt.axvline(x=fft_freqs[peak_low], color='r', linestyle='--')
plt.axvline(x=fft_freqs[peak_high], color='r', linestyle='--')
plt.axvline(x=fft_freqs[dc_high], color='r', linestyle='--')

plt.title("Frequency Spectrum (FFT with Hann Window)")
plt.xlabel("Frequency [MHz]")
plt.ylabel("Magnitude [dB]")
plt.legend()

# Show SINAD & ENOB below the plot
plt.figtext(0.5, 0.01, f"SINAD = {SINAD:.2f} dB    ENOB = {ENOB:.2f} bits",
            ha="center", fontsize=12)

plt.tight_layout(rect=[0,0.03,1,0.95])
plt.show()