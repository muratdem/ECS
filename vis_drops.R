#!/usr/bin/env Rscript
args <- commandArgs(trailingOnly = TRUE)

# 1. Validation and Setup
if (length(args) == 0) {
  stop("Error: No CSV file provided. Usage: Rscript vis_drops.R <filename.csv>")
}

filename <- args[1]
if (!file.exists(filename)) {
  stop(paste("Error: File not found:", filename))
}

# 2. Read Data (FIXED)
# We skip the first line (the broken header) and define names manually.
# Matches the TLA+ output: step, arrivals, completed, shortDrops, longDrops
column_names <- c("step", "arrivals", "completed", "shortDrops", "longDrops")

data <- read.csv(filename, 
                 header = FALSE, 
                 skip = 1,           # Skip the problematic header row
                 col.names = column_names, 
                 sep = ",")

# 3. Validation
required_cols <- c("arrivals", "completed", "shortDrops", "longDrops")
if (!all(required_cols %in% names(data))) {
  stop("Error: CSV is missing required columns. Check TLA+ output format.")
}

runs <- data
num_runs <- nrow(runs)

if (num_runs == 0) {
  stop("Error: CSV contains no data rows.")
}

# Add a Run ID for the X-axis
runs$run_id <- 1:num_runs

# 4. Visualization
svg_file <- gsub("\\.csv$", "_goodput.svg", filename)
svg(svg_file, width = 14, height = 10) # Large canvas for side-by-side bars

# Layout: 2 Rows (Goodput on top, Drops on bottom)
par(mfrow = c(2, 1), mar = c(4, 5, 4, 2) + 0.1)

# --- GRAPH 1: GOODPUT (Arrivals vs Completed) ---
# Prepare Matrix for Barplot: Rows = Variables, Cols = Runs
goodput_matrix <- t(runs[, c("arrivals", "completed")])

# Calculate Y-axis limit
max_y_goodput <- max(goodput_matrix, na.rm = TRUE)
if (!is.finite(max_y_goodput) || max_y_goodput <= 0) max_y_goodput <- 1

# Draw Barplot
bp1 <- barplot(goodput_matrix,
  beside = TRUE,                    # Side-by-side bars
  names.arg = runs$run_id,          # X-axis labels (Run IDs)
  col = c("#D3D3D3", "#2CA02C"),    # Light Gray (Arrivals), Green (Completed)
  main = paste("Goodput Analysis: Incoming Work vs Completed Tasks (", num_runs, " Runs)", sep=""),
  xlab = "Simulation Run ID",
  ylab = "Count",
  ylim = c(0, max_y_goodput * 1.3), # Extra headroom for legend
  border = NA
)

# Add Legend
legend("top", 
       legend = c("Total Arrivals", "Completed (Goodput)"), 
       fill = c("#D3D3D3", "#2CA02C"), 
       bty = "n", ncol = 2, cex = 1.2)

# Optional: Add value labels on top of bars if runs are few (< 20)
if (num_runs < 20) {
  text(bp1, goodput_matrix, round(goodput_matrix,0), pos=3, cex=0.8, col="black")
}


# --- GRAPH 2: LOAD SHEDDING (Short Drops vs Long Drops) ---
drop_matrix <- t(runs[, c("shortDrops", "longDrops")])

# Calculate Y-axis limit
max_y_drops <- max(drop_matrix, na.rm = TRUE)
if (!is.finite(max_y_drops) || max_y_drops <= 0) max_y_drops <- 1

bp2 <- barplot(drop_matrix,
  beside = TRUE,
  names.arg = runs$run_id,
  col = c("#E41A1C", "#377EB8"),    # Red (Short), Blue (Long)
  main = "Load Shedding: Dropped Requests per Run",
  xlab = "Simulation Run ID",
  ylab = "Drop Count",
  ylim = c(0, max_y_drops * 1.3),
  border = NA
)

# Add Legend
legend("top", 
       legend = c("Short Queue Drops (Entry)", "Long Queue Drops (Mid-stream)"), 
       fill = c("#E41A1C", "#377EB8"), 
       bty = "n", ncol = 2, cex = 1.2)

# Add text labels if drops exist
if (max_y_drops > 1 && num_runs < 20) {
   text(bp2, drop_matrix, ifelse(drop_matrix>0, drop_matrix, ""), pos=3, cex=0.8)
}

dev.off()
cat("Visualization created:", svg_file, "\n")