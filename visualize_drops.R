#!/usr/bin/env Rscript
args <- commandArgs(trailingOnly = TRUE)

# 1. Validation and Setup
if (length(args) == 0) {
  stop("Error: No CSV file provided. Usage: Rscript visualize_drops.R <filename.csv>")
}

filename <- args[1]
if (!file.exists(filename)) {
  stop(paste("Error: File not found:", filename))
}

# 2. Read Data (FIXED)
# We skip the first line (the broken header) and define names manually.
column_names <- c("step", "shortDrops", "longDrops", "samples", 
                  "shortWasteNum", "shortWasteDen", "longWasteNum", "longWasteDen", 
                  "shortWasteScaledSum", "longWasteScaledSum")

data <- read.csv(filename, 
                 header = FALSE, 
                 skip = 1,           # Skip the problematic header row
                 col.names = column_names, 
                 sep = ",")

# 3. Data Extraction
runs <- data

if (nrow(runs) == 0) {
  stop("Error: CSV file is empty or contains no valid data rows.")
}

# Helper to safely get mean of a column
get_mean <- function(df, colname) {
  if (colname %in% names(df)) {
    return(mean(df[[colname]], na.rm = TRUE))
  }
  return(0)
}

# --- METRIC 1: DROPS ---
avg_short <- get_mean(runs, "shortDrops")
avg_long  <- get_mean(runs, "longDrops")

# --- METRIC 2: UTILIZATION WASTE (Utilization Lapse) ---
# Formula: (ScaledSum / Samples) / ScaleFactor
# Values are likely scaled by 1,000,000 (ppm) in TLA+
scale_factor <- 1e6 

calc_prob <- function(col_scaled, col_samples) {
  if (col_scaled %in% names(runs) && col_samples %in% names(runs)) {
    # 1. Calculate average value per run: (ScaledSum / Samples)
    #    Protect against division by zero
    safe_samples <- ifelse(runs[[col_samples]] == 0, 1, runs[[col_samples]])
    val_per_run <- runs[[col_scaled]] / safe_samples
    
    # 2. Un-scale the value (convert ppm to probability 0.0-1.0)
    prob_per_run <- val_per_run / scale_factor
    
    # 3. Return the mean across all runs
    return(mean(prob_per_run, na.rm = TRUE))
  }
  return(0)
}

prob_short <- calc_prob("shortWasteScaledSum", "samples")
prob_long  <- calc_prob("longWasteScaledSum", "samples")

# 4. Visualization
svg_file <- gsub("\\.csv$", "_combined.svg", filename)
svg(svg_file, width = 12, height = 6)

# Split Layout: 1 row, 2 columns
par(mfrow = c(1, 2), mar = c(5, 5, 4, 2) + 0.1)

# --- PLOT 1: Average Drops (Bar Plot) ---
counts <- c(avg_short, avg_long)
max_y_drops <- max(counts, na.rm = TRUE)
if (!is.finite(max_y_drops) || max_y_drops <= 0) max_y_drops <- 1

bp_drops <- barplot(counts,
  names.arg = c("Short Drops", "Long Drops"),
  col = c("#E41A1C", "#377EB8"), # Red, Blue
  main = paste("Avg Drops per Run\n(N =", nrow(runs), "Runs)"),
  ylab = "Count",
  ylim = c(0, max_y_drops * 1.25),
  border = NA
)
text(x = bp_drops, y = counts, labels = round(counts, 2), pos = 3, cex = 1.2, font = 2)

# --- PLOT 2: Utilization Lapse Probability (Bar Plot) ---
# Convert fraction to percentage
probs_percent <- c(prob_short, prob_long) * 100
max_y_probs <- max(probs_percent, na.rm = TRUE)
if (!is.finite(max_y_probs) || max_y_probs <= 0) max_y_probs <- 1

bp_probs <- barplot(probs_percent,
  names.arg = c("Short Pool", "Long Pool"),
  col = c("#FF7F0E", "#1F77B4"), # Orange, Light Blue
  main = "Avg Utilization Lapse\n(% Time All Tickets Blocked)",
  ylab = "Probability (%)",
  ylim = c(0, max_y_probs * 1.25),
  border = NA
)

# Format label: "12.45%"
text(
  x = bp_probs, 
  y = probs_percent, 
  labels = sprintf("%.2f%%", probs_percent), 
  pos = 3, cex = 1.2, font = 2
)

dev.off()
cat("Visualization successfully created:", svg_file, "\n")