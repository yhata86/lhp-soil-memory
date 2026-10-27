## Analysis for soil moisture memory at Lambir Hills National Park
## Written by Yoshiaki HATA

# settings ----------------------------------------------------------------

library(data.table)
library(tidyverse)
library(magrittr)
library(zoo)
library(xts)
library(patchwork)
library(minpack.lm)
library(ggtext)
library(gsignal)
library(conflicted)

conflict_prefer("lag", "dplyr")
conflict_prefer("filter", "dplyr")
conflict_prefer("select", "dplyr")
conflict_prefer("between", "dplyr")
conflict_prefer("first", "dplyr")
conflict_prefer("last", "dplyr")
conflict_prefer("year", "lubridate")
conflict_prefer("month", "lubridate")
conflict_prefer("hour", "lubridate")
conflict_prefer("minute", "lubridate")
conflict_prefer("second", "lubridate")
conflict_prefer("yday", "lubridate")


path_data <- "./data/"

timezone <- "Etc/GMT-8"

## standard atmospheric pressure (kPa)
Pa_atm_kPa <- 101.325

## saturated hydraulic conductivity of the soil (mm day-1)
## derived from Kumagai et al. (2004; Water Resources Research)
K_sat_K04 <- 35.6

## coefficient for calculating drainage
## derived from Clapp & Hornberger (1978; Water Resources Research)
b_C78 <- 4.6


# functions ---------------------------------------------------------------

## calculate memory
calc_memory <-
  function(vctr, t_step_hr = 0.5, lag_max = 5000, digit = 1,
           method = "integration") {
    ## calculate autocorrelation
    rslt_acf <- acf(vctr, lag = lag_max, plot = FALSE)
    
    df_rslt_acf <-
      data.frame(acf = rslt_acf$acf,
                 lag = rslt_acf$lag)
    
    ## determine lag range to be integrated
    ## using Trapezoidal approximation of the area under the ACF
    num_row_tail <-
      df_rslt_acf %>% 
      filter(acf <= 0) %>% 
      slice_head() %>% 
      pull(lag)
    
    if (method == "integration") {
      df_rslt_acf %>% 
        slice_head(n = num_row_tail) %>% 
        pull(acf) %>% 
        sum() %>% 
        subtract((df_rslt_acf$acf[1]+df_rslt_acf$acf[num_row_tail])/2) %>%
        multiply_by(t_step_hr) %>% 
        round(digits = digit) %>% 
        return()
    } else if (method == "fitting") {
      df_rslt_acf %>% 
        slice_head(n = num_row_tail) %>% 
        mutate(lag_hr = lag * 0.5) %$% 
        lm(log(acf) ~ lag_hr + 0) %>% 
        summary() %>% 
        .$coef %>% 
        .[1] %>% 
        multiply_by(-1) %>% 
        .^{-1} %>% 
        round(digits = digit) %>% 
        return()
    } else {
      stop("specify appropriate method name")
    }
  }


## high-pass filtering
filter_hp <- function(vctr_xt, freq_sample_Hz, hr_cutoff, amp = 0) {
  NN <- length(vctr_xt)
  xf <- NULL
  xn_FFTf <- NULL
  
  ## generate a time vector
  t <- seq(0, NN-1) * (1/freq_sample_Hz)
  
  ## make sure the mean is zero
  xt_avg0 <- vctr_xt - mean(vctr_xt) 
  
  ## compute the Fourier coefficients of input vector
  xn_FFT <- fft(xt_avg0)
  
  ## cutoff in hours converted to cycles per period
  # n_cut <- round(max(t)/(3600*hr_cutoff)) - 1
  n_cut <- floor(max(t)/(3600*hr_cutoff))
  n_cut <- max(n_cut, 0)
  
  ## set all Fourier coefficients to zero for frequencies smaller than the
  ## cutoff
  xn_FFTf[1:NN] <- xn_FFT[1:NN]
  xn_FFTf[NN+1] <- xn_FFT[1]
  xn_FFTf[1:(n_cut+1)] <- xn_FFTf[1:(n_cut+1)] * amp
  
  ## do the same on the complex-conjugate part
  xn_FFTf[(NN+1-n_cut):(NN+1)] <- xn_FFTf[(NN+1-n_cut):(NN+1)] * amp
  
  ## reconstruct the filtered time series
  xf <- Re(fft(xn_FFTf[1:NN], inverse = TRUE)) / NN
  
  return(xf)
}


## generate artificial precipitation time series by the marked Poisson process
generate_precip <- function(freq, dep, n, seed = 12345) {
  P <- rep(0, n)
  Pr <- rep(0, n)
  
  ## floating-point relative accuracy
  eps <- .Machine$double.eps
  
  set.seed(seed)
  r <- runif(n)
  
  ## generate rainfall event interval vector
  ## by inversion of exponential distribution CDF
  beta <- freq
  tau <- (-1/beta)*(log(1-r+10*eps))
  
  ## generate rainfall event depth vector
  beta <- 1/dep
  eta <- (-1/beta)*(log(1-r+10*eps))
  
  tt <- cumsum(tau)-tau[1]+1
  tti <- floor(tt)
  
  ## replace zero values with the generated depth along with each interval
  P[tti] <- eta
  Pr <- P[1:n]
  
  return(Pr)
}

## calculate daily precipitation statistics
## depth: mean precipitation depth (mm day-1)
## freq: mean frequency of precipitation events (day-1)
calc_precip_stats <- function(vctr_PPT) {
  df <- data.frame(time = seq(1, length(vctr_PPT)),
                   PPT = vctr_PPT)
  
  freq <-
    df %>% 
    dplyr::mutate(flag_start = ifelse(PPT > 0 & lag(PPT) == 0, 1, 0),
                  flag_end = ifelse(PPT == 0 & lag(PPT) > 0, 1, 0),
                  flag_start = ifelse(is.na(flag_start), 0, flag_start),
                  flag_end = ifelse(is.na(flag_end), 0, flag_end)) %>% 
    dplyr::filter(flag_start == 1 | flag_end == 1) %>% 
    dplyr::mutate(intervals = ifelse(flag_start == 1 & lag(flag_end) == 1,
                                     time-lag(time), NA)) %>% 
    dplyr::filter(!is.na(intervals)) %>%
    dplyr::pull(intervals) %>%
    mean() %>% 
    .^{-1}
  
  dep <-
    df %>% 
    dplyr::filter(PPT > 0) %>% 
    dplyr::pull(PPT) %>%
    mean()
  
  return(c(freq, dep))
}


# import half-hourly meteo & flux data ------------------------------------

colname_meteoflux <-
  c("year", "month", "day", "hour", "minute",
    "PPT", "Rs_in", "VPD_60m", "ET_CORR", "Tr", "QC_Tr",
    "SWC_120_La1", "QC_SWC_120_La1")

data_meteoflux <-
  fread(paste0(path_data, "LHP_30min.csv"), header = TRUE, data.table = FALSE,
        col.names = colname_meteoflux) %>% 
  mutate(time = paste(year, month, day, hour, minute) %>% 
           ymd_hm(tz = timezone),
         time_lag = time - 1800)


# import daily data -------------------------------------------------------

colname_meteoflux_daily <-
  c("year", "month", "day",
    "PPT", "Rs_in", "VPD_60m", "ET_CORR", "QC_LE")

data_daily <-
  fread(paste0(path_data, "LHP_daily.csv"), header = FALSE,
        data.table = FALSE, skip = 1, col.names = colname_meteoflux_daily) %>% 
  mutate(date = paste(year, month, day) %>% ymd(tz = timezone),
         DOY = yday(date))


# import MEI.v2 data ------------------------------------------------------

data_MEI <- 
  fread(paste0(path_data, "MEI_v2_JRA3Q.csv"), header = TRUE,
        data.table = FALSE, na.strings = "-9999") %>% 
  mutate(date = ymd(paste(year, month, day), tz = timezone)) %>% 
  select(date, MEI.v2) %>% 
  filter(between(date, ymd("2009/10/01", tz = timezone),
                 ymd("2020/01/01", tz = timezone)))

## interpolate MEI.v2
data_MEI_daily <-
  data.frame(date = seq(first(data_MEI$date), last(data_MEI$date),
                        by = "1 day")) %>% 
  merge.data.frame(., data_MEI, by = "date", all = TRUE) %>% 
  mutate(MEI.v2 = na.approx(MEI.v2)) %>% 
  filter(between(date, ymd("2009/11/01", tz = timezone),
                 ymd("2019/12/31", tz = timezone)))


# merge data set ----------------------------------------------------------

## half-hourly data
data_30min <-
  data_meteoflux %>% 
  select(time, time_lag, PPT, Rs_in, VPD_60m, ET_CORR, Tr, QC_Tr, SWC_120_La1,
         QC_SWC_120_La1) %>% 
  mutate(W_120_La1 = SWC_120_La1 * 1.2 * 1e3)


## daily data
vctr_date_all <- data_daily$date

data_daily <-
  data_30min %>% 
  mutate(QC_SWC_120_La1 = ifelse(QC_SWC_120_La1 > 1, 0, 1)) %>% 
  filter(hour(time) == 0 & minute(time) == 0) %>% 
  select(SWC_120_La1, QC_SWC_120_La1, W_120_La1) %>% 
  mutate(date = c(vctr_date_all[2:length(vctr_date_all)],
                  vctr_date_all[length(vctr_date_all)]+days(1))) %>% 
  merge.data.frame(data_daily, ., by = "date", all.x = TRUE)

data_daily <-
  data_30min %>% 
  select(time_lag, Tr) %>% 
  mutate(Tr = Tr * 1800) %>% 
  read.zoo() %>% 
  as.xts(tzone = timezone) %>% 
  apply.daily(function(x) sapply(x, sum)) %>% 
  coredata() %>% 
  as.data.frame() %>% 
  rename(Tr = V1) %>% 
  bind_cols(data_daily, .)

data_daily <-
  data_30min %>% 
  select(time_lag, QC_Tr) %>% 
  read.zoo() %>% 
  as.xts(tzone = timezone) %>% 
  apply.daily(function(x) sapply(x, mean)) %>% 
  coredata() %>% 
  as.data.frame() %>% 
  rename(QC_Tr = V1) %>% 
  bind_cols(data_daily, .)


# define calculation period -----------------------------------------------

date_all_head <- ymd("2009/11/01", tz = timezone)
date_all_tail <- ymd("2019/12/31", tz = timezone)

time_obs_head <- ymd_hm("2013/05/18 00:30", tz = timezone)
time_obs_tail <- ymd_hm("2017/04/24 00:00", tz = timezone)
date_obs_head <- ymd("2013/05/18", tz = timezone)
date_obs_tail <- ymd("2017/04/23", tz = timezone)

vctr_date_obs <-
  data_daily %>% 
  filter(date >= date_obs_head & date <= date_obs_tail) %>% 
  pull(date)


# spectral analysis for measured variables --------------------------------

## transpiration
wlch_Tr_obs_30min <-
  data_30min %>% 
  filter(time >= time_obs_head & time <= time_obs_tail) %$% 
  pwelch(Tr, window = round(length(Tr)/4), fs = 2,
         detrend = "long-mean")

var_Tr_obs_30min <-
  data_30min %>% 
  filter(time >= time_obs_head & time <= time_obs_tail) %$% 
  var(Tr)

df_wlch_Tr_obs_30min <-
  data.frame(freq = wlch_Tr_obs_30min$freq,
             spec = wlch_Tr_obs_30min$spec) %>% 
  mutate(spec_n = spec / var_Tr_obs_30min) %>% 
  filter(freq > 0)

lm_Tr_30min <-
  df_wlch_Tr_obs_30min %>% 
  filter(freq >= 1/24 & freq <= 1/1) %>%
  mutate(freq_log = log10(freq),
         spec_n_log = log10(spec_n)) %$% 
  lm(spec_n_log ~ freq_log) %>% 
  summary()


## soil water storage
wlch_W_obs_30min <-
  data_30min %>% 
  filter(time >= time_obs_head & time <= time_obs_tail) %$% 
  pwelch(W_120_La1, window = round(nrow(.)/4), fs = 2,
         detrend = "long-mean")

var_W_obs_30min <-
  data_30min %>% 
  filter(time >= time_obs_head & time <= time_obs_tail) %$% 
  var(W_120_La1)

df_wlch_W_obs_30min <-
  data.frame(freq = wlch_W_obs_30min$freq,
             spec = wlch_W_obs_30min$spec) %>% 
  mutate(spec_n = spec / var_W_obs_30min) %>% 
  filter(freq > 0)

lm_W_obs_30min <-
  df_wlch_W_obs_30min %>% 
  filter(freq >= 1/24 & freq <= 1/1) %>%
  mutate(freq_log = log10(freq),
         spec_n_log = log10(spec_n)) %$% 
  lm(spec_n_log ~ freq_log) %>% 
  summary()


## precipitation
wlch_PPT_30min <-
  data_30min %$% 
  pwelch(PPT, window = nrow(.)/4, fs = 2, detrend = "long-mean")

var_PPT_30min <-
  data_30min %$% 
  var(PPT)

df_wlch_PPT_30min <-
  data.frame(freq = wlch_PPT_30min$freq,
             spec = wlch_PPT_30min$spec) %>% 
  mutate(spec_n = spec / var_PPT_30min) %>% 
  filter(freq > 0)

lm_PPT_30min <-
  df_wlch_PPT_30min %>% 
  filter(freq >= 1/24 & freq <= 1/1) %>%
  mutate(freq_log = log10(freq),
         spec_n_log = log10(spec_n)) %$% 
  lm(spec_n_log ~ freq_log) %>% 
  summary()

Enp_avg_white_30min <-
  df_wlch_PPT_30min %>% 
  filter(freq >= 1/8760 & freq <= 1/24) %>%
  mutate(spec_n_log = log10(spec_n)) %$% 
  mean(spec_n)


## solar radiation
wlch_Rs_30min <-
  data_30min %$% 
  pwelch(Rs_in, window = nrow(.)/4, fs = 2, detrend = "long-mean")

var_Rs_30min <-
  data_30min %$% 
  var(Rs_in)

df_wlch_Rs_30min <-
  data.frame(freq = wlch_Rs_30min$freq,
             spec = wlch_Rs_30min$spec) %>% 
  mutate(spec_n = spec / var_Rs_30min) %>% 
  filter(freq > 0)

lm_Rs_30min <-
  df_wlch_Rs_30min %>% 
  filter(freq >= 1/24 & freq <= 1/1) %>%
  mutate(freq_log = log10(freq),
         spec_n_log = log10(spec_n)) %$% 
  lm(spec_n_log ~ freq_log) %>% 
  summary()


## VPD
wlch_VPD_30min <-
  data_30min %$% 
  pwelch(VPD_60m, window = nrow(.)/4, fs = 2, detrend = "long-mean")

var_VPD_30min <-
  data_30min %$% 
  var(VPD_60m)

df_wlch_VPD_30min <-
  data.frame(freq = wlch_VPD_30min$freq,
             spec = wlch_VPD_30min$spec) %>% 
  mutate(spec_n = spec / var_VPD_30min) %>% 
  filter(freq > 0)

lm_VPD_30min <-
  df_wlch_VPD_30min %>% 
  filter(freq >= 1/24 & freq <= 1/1) %>%
  mutate(freq_log = log10(freq),
         spec_n_log = log10(spec_n)) %$% 
  lm(spec_n_log ~ freq_log) %>% 
  summary()


## evapotranspiration
wlch_ET_30min <-
  data_30min %$% 
  pwelch(ET_CORR, window = nrow(.)/4, fs = 2, detrend = "long-mean")

var_ET_30min <-
  data_30min %$% 
  var(ET_CORR)

df_wlch_ET_30min <-
  data.frame(freq = wlch_ET_30min$freq,
             spec = wlch_ET_30min$spec) %>% 
  mutate(spec_n = spec / var_ET_30min) %>% 
  filter(freq > 0)

lm_ET_30min <-
  df_wlch_ET_30min %>% 
  filter(freq >= 1/24 & freq <= 1/1) %>%
  mutate(freq_log = log10(freq),
         spec_n_log = log10(spec_n)) %$% 
  lm(spec_n_log ~ freq_log) %>% 
  summary()


# draw power spectra of measured variables --------------------------------

size_axis_text <- 10
size_axis_title <- 12
lwd_power <- 0.5
lwd_vline <- 0.1
lwd_lm <- 0.5
size_anno <- 4

beta_DM88 <- 2*pi/(7.3/12*365*24)
separation_DM88 <- 2*pi/beta_DM88


p_wlch_W_30min <-
  data.frame(xxx = 10^seq(-5, 0, by = 0.01)) %>% 
  mutate(yyy = 4*beta_DM88 / ((2*pi*xxx)^2+beta_DM88^2)) %>% 
  ggplot()+
  theme_classic()+
  theme(axis.title = element_text(size = size_axis_title),
        axis.text.x = element_blank(),
        axis.text.y = element_text(size = size_axis_text, colour = "black"),
        axis.ticks = element_line(colour = "black"),
        axis.ticks.length = unit(3, "mm"))+
  labs(x = "",
       y = bquote( italic(E[nw])(italic(f)) ))+
  scale_x_log10(limits = c(1e-5, 1e0),
                breaks = c(1e-5, 1e-4, 1e-3, 1e-2, 1e-1, 1e0),
                labels = c("", bquote(10^{-4}), "", bquote(10^{-2}),
                           "", bquote(10^0)),
                expand = expansion())+
  scale_y_log10(limits = c(1e-5, 1e4),
                breaks = c(1e-5, 1e-4, 1e-3, 1e-2, 1e-1, 1e0, 1e1, 1e2, 1e3,
                           1e4),
                labels = c("", bquote(10^{-4}), "", bquote(10^{-2}),
                           "", bquote(10^0), "", bquote(10^2),
                           "", bquote(10^4)),
                expand = expansion())+
  geom_line(data = df_wlch_W_obs_30min, aes(freq, spec_n), col = "tan4",
            lwd = lwd_power, alpha = 0.8)+
  geom_line(aes(xxx, yyy), col = "black",
            lwd = lwd_power, alpha = 0.8, lty = "dashed")+
  geom_abline(slope = lm_W_obs_30min$coef[2, 1],
              intercept = lm_W_obs_30min$coef[1, 1], col = "black",
              lwd = lwd_lm)+
  geom_abline(slope = -2 + round(lm_PPT_30min$coef[2, 1], 3),
              intercept = lm_W_obs_30min$coef[1, 1], col = "black",
              lwd = lwd_lm, alpha = 0.8, lty = "dashed")+
  geom_vline(xintercept = 1/12, col = "black", lwd = lwd_vline,
             lty = "dotted")+
  geom_vline(xintercept = 1/24, col = "black", lwd = lwd_vline,
             lty = "dotted")+
  geom_vline(xintercept = 1/720, col = "black", lwd = lwd_vline,
             lty = "dotted")+
  geom_vline(xintercept = 1/8760, col = "black", lwd = lwd_vline,
             lty = "dotted")+
  annotate("text", x = 10^{-2.6}, y = 10^2.8,
           label = paste0("italic(f)^", round(lm_W_obs_30min$coef[2, 1], 2)),
           parse = TRUE, col = "black", size = size_anno, hjust = 0)+
  annotate("text", x = Inf, y = Inf, label = "(a)", col = "black",
           size = size_anno, hjust = 1, vjust = 1)


p_wlch_PPT_30min_all <-
  ggplot()+
  theme_classic()+
  theme(axis.title = element_text(size = size_axis_title),
        axis.text.x = element_blank(),
        axis.text.y = element_text(size = size_axis_text, colour = "black"),
        axis.ticks = element_line(colour = "black"),
        axis.ticks.length = unit(3, "mm"))+
  labs(x = "",
       y = bquote( italic(E[nP])(italic(f)) ))+
  coord_cartesian(clip = "off")+
  scale_x_log10(limits = c(1e-5, 1e0),
                breaks = c(1e-5, 1e-4, 1e-3, 1e-2, 1e-1, 1e0),
                labels = c("", bquote(10^{-4}), "", bquote(10^{-2}),
                           "", bquote(10^0)),
                expand = expansion())+
  scale_y_log10(limits = c(1e-2, 1e3),
                breaks = c(1e-2, 1e-1, 1e0, 1e1, 1e2),
                labels = c(bquote(10^{-2}), "", bquote(10^0), "",
                           bquote(10^2)),
                expand = expansion())+
  geom_line(data = df_wlch_PPT_30min, aes(freq, spec_n), col = "navyblue",
            lwd = lwd_power, alpha = 0.6)+
  geom_abline(slope = lm_PPT_30min$coef[2, 1],
              intercept = lm_PPT_30min$coef[1, 1], col = "black",
              lwd = lwd_lm)+
  geom_hline(yintercept = Enp_avg_white_30min, col = "black",
             lwd = lwd_lm, lty = "dashed")+
  geom_vline(xintercept = 1/12, col = "black", lwd = lwd_vline,
             lty = "dotted")+
  geom_vline(xintercept = 1/24, col = "black", lwd = lwd_vline,
             lty = "dotted")+
  geom_vline(xintercept = 1/720, col = "black", lwd = lwd_vline,
             lty = "dotted")+
  geom_vline(xintercept = 1/8760, col = "black", lwd = lwd_vline,
             lty = "dotted")+
  annotate("text", x = 10^{-3.3}, y = 10^2.65,
           label = paste0("italic(f)^", round(lm_PPT_30min$coef[2, 1], 2)),
           parse = TRUE, col = "black", size = size_anno, hjust = 0)+
  annotate("text", x = 10^{-4.8}, y = 10^0.15,
           label = "italic(f)^0",
           parse = TRUE, col = "black", size = size_anno, hjust = 0)+
  annotate("text", x = Inf, y = Inf, label = "(b)", col = "black",
           size = size_anno, hjust = 1, vjust = 1)


p_wlch_ET_30min <-
  ggplot()+
  theme_classic()+
  theme(axis.title = element_text(size = size_axis_title),
        axis.text.x = element_blank(),
        axis.text.y = element_text(size = size_axis_text, colour = "black"),
        axis.ticks = element_line(colour = "black"),
        axis.ticks.length = unit(3, "mm"))+
  labs(x = "",
       y = bquote( italic(E[nET])(italic(f)) ))+
  scale_x_log10(limits = c(1e-5, 1e0),
                breaks = c(1e-5, 1e-4, 1e-3, 1e-2, 1e-1, 1e0),
                labels = c("", bquote(10^{-4}), "", bquote(10^{-2}),
                           "", bquote(10^0)),
                expand = expansion())+
  scale_y_log10(limits = c(1e-2, 1e4),
                breaks = c(1e-2, 1e-1, 1e0, 1e1, 1e2, 1e3,
                           1e4),
                labels = c(bquote(10^{-2}),
                           "", bquote(10^0), "", bquote(10^2),
                           "", bquote(10^4)),
                expand = expansion())+
  geom_line(data = df_wlch_ET_30min, aes(freq, spec_n), col = "royalblue",
            lwd = lwd_power, alpha = 0.8)+
  geom_abline(slope = lm_ET_30min$coef[2, 1],
              intercept = lm_ET_30min$coef[1, 1], col = "black",
              lwd = lwd_lm)+
  geom_vline(xintercept = 1/12, col = "black", lwd = lwd_vline,
             lty = "dotted")+
  geom_vline(xintercept = 1/24, col = "black", lwd = lwd_vline,
             lty = "dotted")+
  geom_vline(xintercept = 1/720, col = "black", lwd = lwd_vline,
             lty = "dotted")+
  geom_vline(xintercept = 1/8760, col = "black", lwd = lwd_vline,
             lty = "dotted")+
  annotate("text", x = 10^{-4.5}, y = 10^3.0,
           label = paste0("italic(f)^", round(lm_ET_30min$coef[2, 1], 2)),
           parse = TRUE, col = "black", size = size_anno, hjust = 0)+
  annotate("text", x = Inf, y = Inf, label = "(c)", col = "black",
           size = size_anno, hjust = 1, vjust = 1)


p_wlch_Tr_30min <-
  ggplot()+
  theme_classic()+
  theme(axis.title = element_text(size = size_axis_title),
        axis.text.x = element_text(size = size_axis_text, colour = "black"),
        axis.text.y = element_text(size = size_axis_text, colour = "black"),
        axis.ticks = element_line(colour = "black"),
        axis.ticks.length = unit(3, "mm"))+
  labs(x = bquote( italic(f)~(h^{-1}) ),
       y = bquote( italic(E)[italic(nT)[r]](italic(f)) ))+
  coord_cartesian(clip = "off")+
  scale_x_log10(limits = c(1e-5, 1e0),
                breaks = c(1e-5, 1e-4, 1e-3, 1e-2, 1e-1, 1e0),
                labels = c("", bquote(10^{-4}), "", bquote(10^{-2}),
                           "", bquote(10^0)),
                expand = expansion())+
  scale_y_log10(limits = c(1e-5, 1e4),
                breaks = c(1e-5, 1e-4, 1e-3, 1e-2, 1e-1, 1e0, 1e1, 1e2, 1e3,
                           1e4),
                labels = c("", bquote(10^{-4}), "", bquote(10^{-2}),
                           "", bquote(10^0), "", bquote(10^2),
                           "", bquote(10^4)),
                expand = expansion())+
  geom_line(data = df_wlch_Tr_obs_30min, aes(freq, spec_n), col = "skyblue",
            lwd = lwd_power, alpha = 0.8)+
  geom_abline(slope = lm_Tr_30min$coef[2, 1],
              intercept = lm_Tr_30min$coef[1, 1], col = "black",
              lwd = lwd_lm)+
  geom_vline(xintercept = 1/12, col = "black", lwd = lwd_vline,
             lty = "dotted")+
  geom_vline(xintercept = 1/24, col = "black", lwd = lwd_vline,
             lty = "dotted")+
  geom_vline(xintercept = 1/720, col = "black", lwd = lwd_vline,
             lty = "dotted")+
  geom_vline(xintercept = 1/8760, col = "black", lwd = lwd_vline,
             lty = "dotted")+
  annotate("text", x = 10^{-2.3}, y = 10^3.8,
           label = paste0("italic(f)^", round(lm_Tr_30min$coef[2, 1], 2)),
           parse = TRUE, col = "black", size = size_anno, hjust = 0)+
  annotate("text", x = Inf, y = Inf, label = "(d)", col = "black",
           size = size_anno, hjust = 1, vjust = 1)


p_wlch_Rs_30min_all <-
  ggplot()+
  theme_classic()+
  theme(axis.title = element_text(size = size_axis_title),
        axis.text.x = element_text(size = size_axis_text, colour = "black"),
        axis.text.y = element_text(size = size_axis_text, colour = "black"),
        axis.ticks = element_line(colour = "black"),
        axis.ticks.length = unit(3, "mm"))+
  labs(x = bquote( italic(f)~(h^{-1}) ),
       y = bquote( italic(E)[italic(nR)[s]](italic(f)) ))+
  scale_x_log10(limits = c(1e-5, 1e0),
                breaks = c(1e-5, 1e-4, 1e-3, 1e-2, 1e-1, 1e0),
                labels = c("", bquote(10^{-4}), "", bquote(10^{-2}),
                           "", bquote(10^0)),
                expand = expansion())+
  scale_y_log10(limits = c(1e-3, 1e4),
                breaks = c(1e-3, 1e-2, 1e-1, 1e0, 1e1, 1e2, 1e3, 1e4),
                labels = c("", bquote(10^{-2}), "", bquote(10^0),
                           "", bquote(10^2), "", bquote(10^4)),
                expand = expansion(0.05))+
  geom_line(data = df_wlch_Rs_30min, aes(freq, spec_n), col = "indianred",
            lwd = lwd_power, alpha = 0.8)+
  geom_abline(slope = lm_Rs_30min$coef[2, 1],
              intercept = lm_Rs_30min$coef[1, 1], col = "black",
              lwd = lwd_lm)+
  geom_vline(xintercept = 1/12, col = "black", lwd = lwd_vline,
             lty = "dotted")+
  geom_vline(xintercept = 1/24, col = "black", lwd = lwd_vline,
             lty = "dotted")+
  geom_vline(xintercept = 1/720, col = "black", lwd = lwd_vline,
             lty = "dotted")+
  geom_vline(xintercept = 1/8760, col = "black", lwd = lwd_vline,
             lty = "dotted")+
  annotate("text", x = 10^{-3.8}, y = 10^3.8,
           label = paste0("italic(f)^", round(lm_Rs_30min$coef[2, 1], 2)),
           parse = TRUE, col = "black", size = size_anno, hjust = 0)+
  annotate("text", x = Inf, y = Inf, label = "(e)", col = "black",
           size = size_anno, hjust = 1, vjust = 1)


p_wlch_VPD_30min_all <-
  ggplot()+
  theme_classic()+
  theme(axis.title = element_text(size = size_axis_title),
        axis.text.x = element_text(size = size_axis_text, colour = "black"),
        axis.text.y = element_text(size = size_axis_text, colour = "black"),
        axis.ticks = element_line(colour = "black"),
        axis.ticks.length = unit(3, "mm"))+
  labs(x = bquote( italic(f)~(h^{-1}) ),
       y = bquote( italic(E[nD])(italic(f)) ))+
  coord_cartesian(clip = "off")+
  scale_x_log10(limits = c(1e-5, 1e0),
                breaks = c(1e-5, 1e-4, 1e-3, 1e-2, 1e-1, 1e0),
                labels = c("", bquote(10^{-4}), "", bquote(10^{-2}),
                           "", bquote(10^0)),
                expand = expansion())+
  scale_y_log10(limits = c(1e-3, 1e4),
                breaks = c(1e-3, 1e-2, 1e-1, 1e0, 1e1, 1e2, 1e3, 1e4),
                labels = c("", bquote(10^{-2}), "", bquote(10^0),
                           "", bquote(10^2), "", bquote(10^4)),
                expand = expansion(0.05))+
  geom_line(data = df_wlch_VPD_30min, aes(freq, spec_n), col = "turquoise4",
            lwd = lwd_power, alpha = 0.8)+
  geom_abline(slope = lm_VPD_30min$coef[2, 1],
              intercept = lm_VPD_30min$coef[1, 1], col = "black",
              lwd = lwd_lm)+
  geom_vline(xintercept = 1/12, col = "black", lwd = lwd_vline,
             lty = "dotted")+
  geom_vline(xintercept = 1/24, col = "black", lwd = lwd_vline,
             lty = "dotted")+
  geom_vline(xintercept = 1/720, col = "black", lwd = lwd_vline,
             lty = "dotted")+
  geom_vline(xintercept = 1/8760, col = "black", lwd = lwd_vline,
             lty = "dotted")+
  annotate("text", x = 10^{-2.6}, y = 10^4,
           label = paste0("italic(f)^", round(lm_VPD_30min$coef[2, 1], 2)),
           parse = TRUE, col = "black", size = size_anno, hjust = 0,
           vjust = 0.4)+
  annotate("text", x = Inf, y = Inf, label = "(f)", col = "black",
           size = size_anno, hjust = 1, vjust = 1)


p_wlch_meteo_30min_all <-
  (p_wlch_W_30min | p_wlch_PPT_30min_all | p_wlch_ET_30min) /
  (p_wlch_Tr_30min | p_wlch_Rs_30min_all | p_wlch_VPD_30min_all)

p_wlch_meteo_30min_all

# ggsave(file = "./LHP_powerspec_meteo_30min_ver04.pdf",
#        plot = p_wlch_meteo_30min_all, width = 190, height = 120,
#        units = "mm", device = cairo_pdf)


# MEI and low-frequency PPT relationship ----------------------------------

## estimate an optimal cut-off day
vctr_days_MEI <- NULL
vctr_R2_MEI <- NULL

for (i in 1:(365*5)) {
  vctr_days_MEI[i] <- i
  
  PPT_daily <- data_daily %>% pull(PPT)
  PPT_daily_hp_avg0 <-
    PPT_daily %>% filter_hp(., 1/86400, 24*vctr_days_MEI[i])
  PPT_daily_lp <- PPT_daily - PPT_daily_hp_avg0
  
  vctr_R2_MEI[i] <- 
    data.frame(PPT_lp = PPT_daily_lp,
               MEI = data_MEI_daily$MEI) %>% 
    filter(MEI > 0.5 | MEI < -0.5) %$% 
    lm(PPT_lp ~ MEI) %>% 
    summary() %>% 
    .$adj.r.squared
}

days_cutoff <-
  data.frame(days_cutoff = vctr_days_MEI,
             R2 = vctr_R2_MEI) %>% 
  arrange(desc(R2)) %>% 
  slice_head() %>% 
  pull(days_cutoff)

## apply low-pass filter
PPT_daily <- data_daily %>% pull(PPT)
PPT_daily_hp_avg0 <-
  PPT_daily %>% filter_hp(., 1/86400, 24*days_cutoff)
PPT_daily_lp_avg0 <- PPT_daily - PPT_daily_hp_avg0 - mean(PPT_daily)


## draw time series
## for x-axis label
df_label <-
  data.frame(date = c(ymd("2010/07/01", tz = timezone),
                      ymd("2011/07/01", tz = timezone),
                      ymd("2012/07/01", tz = timezone),
                      ymd("2013/07/01", tz = timezone),
                      ymd("2014/07/01", tz = timezone),
                      ymd("2015/07/01", tz = timezone),
                      ymd("2016/07/01", tz = timezone),
                      ymd("2017/07/01", tz = timezone),
                      ymd("2018/07/01", tz = timezone),
                      ymd("2019/07/01", tz = timezone))) %>% 
  mutate(yval = -2.7,
         label_yr = seq(2010, 2019))


p_MEI_PPT_ts <-
  data.frame(date = vctr_date_all,
             MEI = data_MEI_daily$MEI.v2,
             PPT_lp = PPT_daily_lp_avg0) %>% 
  mutate(thres_up = 0.5,
         thres_dw = -0.5,
         thres_up = ifelse(MEI >= thres_up, thres_up, NA),
         thres_dw = ifelse(MEI <= thres_dw, thres_dw, NA)) %>% 
  ggplot()+
  theme_classic()+
  theme(axis.title.y = element_markdown(size = 14),
        axis.text.x = element_blank(),
        axis.text.y = element_text(size = 12, colour = "black"),
        axis.ticks = element_line(colour = "black"),
        axis.ticks.length = unit(3, "mm"))+
  labs(x = "",
       y = "Precipitation fluctuation (mm day<sup>-1</sup>)<br> or MEI.v2")+
  coord_cartesian(clip = "off")+
  scale_x_datetime(date_breaks = "1 year", date_labels = "%Y",
                   expand = expansion())+
  scale_y_continuous(limits = c(-2.7, 2.5), breaks = seq(-2, 2),
                     labels = c(-2, "", 0, "", 2), expand = expansion())+
  geom_ribbon(aes(x = date, ymin = thres_up, ymax = MEI), fill = "red3",
              alpha = 0.5)+
  geom_ribbon(aes(x = date, ymin = MEI, ymax = thres_dw), fill = "royalblue",
              alpha = 0.5)+
  geom_line(aes(date, PPT_lp), col = "navyblue", lwd = 1)+
  geom_line(aes(date, MEI), col = "black", lwd = 0.5)+
  geom_hline(yintercept = 0.5, col = "black", lty = "dashed")+
  geom_hline(yintercept = -0.5, col = "black", lty = "dashed")+
  geom_text(data = df_label, aes(date, yval, label = label_yr),
            size = 4, col = "black", vjust = 1.6)+
  annotate("text", x = ymd_hm("2011/05/15 00:00", tz = timezone), y = -1.8,
           label = "La Niña", hjust = 0, col = "royalblue", size = 5)+
  annotate("text", x = ymd_hm("2015/05/01 00:00", tz = timezone), y = 2.1,
           label = "El Niño", hjust = 1, col = "red3", size = 5)

p_MEI_PPT_ts

# ggsave(file = "./LHP_MEI_PPT_ts_ver01.pdf",
#        plot = p_MEI_PPT_ts, width = 190, height = 100,
#        units = "mm", device = cairo_pdf)


# check correlation among daily meteo time series -------------------------

## linear regression
lm_VPD_PPT <-
  data_daily %>% 
  mutate(VPD_60m_kPa = 0.1*VPD_60m) %>% 
  filter(PPT > 0) %$% 
  lm(VPD_60m_kPa ~ PPT) %>% 
  summary()

lm_Rs_PPT <-
  data_daily %>% 
  filter(PPT > 0) %$% 
  lm(Rs_in ~ PPT) %>% 
  summary()

lm_Rs_VPD <-
  data_daily %>% 
  mutate(VPD_60m_kPa = 0.1*VPD_60m) %>% 
  filter(PPT > 0) %$% 
  lm(Rs_in ~ VPD_60m_kPa) %>% 
  summary()

slp_VPD_PPT <- coef(lm_VPD_PPT)[2, 1] %>% round(digits = 3)
int_VPD_PPT <- coef(lm_VPD_PPT)[1, 1] %>% round(digits = 3)
R2_VPD_PPT <- lm_VPD_PPT$adj.r.squared %>% round(digits = 3)

slp_Rs_PPT <- coef(lm_Rs_PPT)[2, 1] %>% round(digits = 3)
int_Rs_PPT <- coef(lm_Rs_PPT)[1, 1] %>% round(digits = 3)
R2_Rs_PPT <- lm_Rs_PPT$adj.r.squared %>% round(digits = 3)

slp_Rs_VPD <- coef(lm_Rs_VPD)[2, 1] %>% round(digits = 3)
int_Rs_VPD <- coef(lm_Rs_VPD)[1, 1] %>% round(digits = 3)
R2_Rs_VPD <- lm_Rs_VPD$adj.r.squared %>% round(digits = 3)


## draw scatter plots
size_axis_title <- 14
size_axis_text <- 12
size_anno_fignum <- 4
size_eq <- 3
size_point <- 1

p_1by1_VPD_PPT <-
  data_daily %>% 
  mutate(VPD_60m_kPa = 0.1*VPD_60m) %>% 
  filter(PPT > 0) %>% 
  ggplot()+
  theme_classic()+
  theme(axis.title = element_text(size = size_axis_title),
        axis.text.x = element_blank(),
        axis.text.y = element_text(size = size_axis_text, colour = "black"),
        axis.ticks = element_line(colour = "black"),
        axis.ticks.length = unit(3, "mm"))+
  labs(x = "",
       y = bquote( italic(D)~(kPa) ))+
  scale_x_continuous(limits = c(0, 255), breaks = seq(0, 250, by = 50),
                     labels = c(0, "", 100, "", 200, ""),
                     expand = expansion())+
  scale_y_continuous(limits = c(0, 1.6), breaks = seq(0, 1.5, by = 0.5),
                     labels = c(0, "", 1, ""),
                     expand = expansion())+
  geom_point(aes(PPT, VPD_60m_kPa), col = "deepskyblue4", size = size_point,
             alpha = 0.3)+
  geom_abline(slope = coef(lm_VPD_PPT)[2, 1],
              intercept = coef(lm_VPD_PPT)[1, 1],
              col = "black", lwd = 0.8, alpha = 0.4)+
  annotate("text", x = -Inf, y = Inf,
           label = "(a)", col = "black", size = size_anno_fignum, hjust = -0.1,
           vjust = 1)+
  annotate("text", x = 160, y = 1.5,
           label = paste0("italic(y) ==", slp_VPD_PPT, "*italic(x)+",
                          int_VPD_PPT),
           parse = TRUE, col = "black", size = size_eq, hjust = 0)+
  annotate("text", x = 160, y = 1.36,
           label = paste0("italic(R)^2 ==", R2_VPD_PPT),
           parse = TRUE, col = "black", size = size_eq, hjust = 0)


p_1by1_Rs_PPT <-
  data_daily %>% 
  filter(PPT > 0) %>% 
  ggplot()+
  theme_classic()+
  theme(axis.title = element_text(size = size_axis_title),
        axis.text.x = element_text(size = size_axis_text, colour = "black"),
        axis.text.y = element_text(size = size_axis_text, colour = "black"),
        axis.ticks = element_line(colour = "black"),
        axis.ticks.length = unit(3, "mm"))+
  labs(x = bquote( italic(P)~(mm~day^{-1}) ),
       y = bquote( italic(R)[s]~(MJ~m^{-2}~day^{-1}) ))+
  scale_x_continuous(limits = c(0, 255), breaks = seq(0, 250, by = 50),
                     labels = c(0, "", 100, "", 200, ""),
                     expand = expansion())+
  scale_y_continuous(limits = c(0, 27), breaks = seq(0, 25, by = 5),
                     labels = c(0, "", 10, "", 20, ""),
                     expand = expansion())+
  geom_point(aes(PPT, Rs_in), col = "darkorchid3", size = size_point,
             alpha = 0.3)+
  geom_abline(slope = coef(lm_Rs_PPT)[2, 1],
              intercept = coef(lm_Rs_PPT)[1, 1],
              col = "black", lwd = 0.8, alpha = 0.4)+
  annotate("text", x = -Inf, y = Inf,
           label = "(b)", col = "black", size = size_anno_fignum, hjust = -0.1,
           vjust = 1)+
  annotate("text", x = 160, y = 25.94,
           label = paste0("italic(y) ==", slp_Rs_PPT, "*italic(x)+",
                          int_Rs_PPT),
           parse = TRUE, col = "black", size = size_eq, hjust = 0)+
  annotate("text", x = 160, y = 23.68,
           label = paste0("italic(R)^2 ==", R2_Rs_PPT),
           parse = TRUE, col = "black", size = size_eq, hjust = 0)


p_1by1_Rs_VPD <-
  data_daily %>% 
  mutate(VPD_60m_kPa = 0.1*VPD_60m) %>% 
  filter(PPT > 0) %>% 
  ggplot()+
  theme_classic()+
  theme(axis.title = element_text(size = size_axis_title),
        axis.text.x = element_text(size = size_axis_text, colour = "black"),
        axis.text.y = element_blank(),
        axis.ticks = element_line(colour = "black"),
        axis.ticks.length = unit(3, "mm"))+
  labs(x = bquote( italic(D)~(kPa) ),
       y = "")+
  scale_x_continuous(limits = c(0, 1.6), breaks = seq(0, 1.5, by = 0.5),
                     labels = c(0, "", 1, ""),
                     expand = expansion())+
  scale_y_continuous(limits = c(0, 27), breaks = seq(0, 25, by = 5),
                     labels = c(0, "", 10, "", 20, ""),
                     expand = expansion())+
  geom_point(aes(VPD_60m_kPa, Rs_in), col = "coral3", size = size_point,
             alpha = 0.3)+
  geom_abline(slope = coef(lm_Rs_VPD)[2, 1],
              intercept = coef(lm_Rs_VPD)[1, 1],
              col = "black", lwd = 0.8, alpha = 0.4)+
  annotate("text", x = -Inf, y = Inf,
           label = "(c)", col = "black", size = size_anno_fignum, hjust = -0.1,
           vjust = 1)+
  annotate("text", x = 1.05, y = 5,
           label = paste0("italic(y) ==", slp_Rs_VPD, "*italic(x)+",
                          int_Rs_VPD),
           parse = TRUE, col = "black", size = size_eq, hjust = 0)+
  annotate("text", x = 1.05, y = 2.7,
           label = paste0("italic(R)^2 ==", R2_Rs_VPD),
           parse = TRUE, col = "black", size = size_eq, hjust = 0)


p_1by1_meteo <-
  wrap_plots(p_1by1_VPD_PPT, plot_spacer(), p_1by1_Rs_PPT, p_1by1_Rs_VPD,
             nrow = 2)

p_1by1_meteo

# ggsave(file = "./LHP_meteo_daily_1by1_ver01.pdf",
#        plot = p_1by1_meteo, width = 190, height = 120,
#        units = "mm", device = cairo_pdf)


# scatter plot for ET and transpiration -----------------------------------

## linear regression
lm_ET_Tr <-
  data_daily %>% 
  filter(date >= date_obs_head & date <= date_obs_tail &
           PPT == 0 & QC_LE >= 0.5 & QC_Tr >= 0.5) %$% 
  lm(ET_CORR ~ Tr) %>% 
  summary()

slp_ET <- coef(lm_ET_Tr)[2, 1] %>% round(digits = 2)
int_ET <- coef(lm_ET_Tr)[1, 1] %>% round(digits = 2)
R2_ET <- lm_ET_Tr$adj.r.squared %>% round(digits = 2)


## draw a scatter plot
p_1by1_ET_Tr <-
  data_daily %>% 
  filter(date >= date_obs_head & date <= date_obs_tail &
           PPT == 0 & QC_LE >= 0.5 & QC_Tr >= 0.5) %>% 
  ggplot()+
  theme_classic()+
  theme(axis.title = element_text(size = 14),
        axis.text.x = element_text(size = 12, colour = "black"),
        axis.text.y = element_text(size = 12, colour = "black"),
        axis.ticks = element_line(colour = "black"),
        axis.ticks.length = unit(3, "mm"))+
  labs(x = bquote( italic("T")[r]~(mm~day^{-1}) ),
       y = bquote( italic(ET)~(mm~day^{-1}) ))+
  coord_fixed()+
  scale_x_continuous(limits = c(0, 7), breaks = seq(0, 7, by = 1),
                     labels = c(0, "", 2, "", 4, "", 6, ""),
                     expand = expansion())+
  scale_y_continuous(limits = c(0, 7), breaks = seq(0, 7, by = 1),
                     labels = c(0, "", 2, "", 4, "", 6, ""),
                     expand = expansion())+
  geom_point(aes(Tr, ET_CORR), col = "royalblue", size = 2,
             alpha = 0.3)+
  geom_abline(slope = coef(lm_ET_Tr)[2, 1],
              intercept = coef(lm_ET_Tr)[1, 1],
              col = "gray40", lwd = 1.2, alpha = 0.8)+
  geom_abline(slope = 1, intercept = 0, col = "black", lty = "dashed")+
  annotate("text", x = 0.35, y = 6.6,
           label = paste0("italic(y) ==", slp_ET, "*italic(x)+", int_ET),
           parse = TRUE, col = "black", size = 4, hjust = 0)+
  annotate("text", x = 0.35, y = 6.1,
           label = paste0("italic(R)^2 ==", R2_ET),
           parse = TRUE, col = "black", size = 4, hjust = 0)

p_1by1_ET_Tr

# ggsave(file = "./LHP_ET_Tr_1by1_ver02.pdf",
#        plot = p_1by1_ET_Tr, width = 100, height = 100,
#        units = "mm", device = cairo_pdf)


# empirical modeling for transpiration ------------------------------------

## calculate predetermined parameters
theta_max <-
  data_daily %>%
  filter(date >= date_obs_head & date <= date_obs_tail) %>%
  pull(SWC_120_La1) %>%
  max()

Rs_in_max <-
  data_daily %>%
  filter(date >= date_obs_head & date <= date_obs_tail) %>%
  pull(Rs_in) %>%
  max()


## fit parameters
jarvis <- function(param, Rs, VPD_kPa, theta) {
  param$g_ref * Rs*(Rs_in_max+param$a1)/(Rs_in_max*(Rs+param$a1)) *
    theta*(theta_max+param$a2)/(theta_max*(theta+param$a2)) *
    (1-param$m*log(VPD_kPa))
}

resid <-
  function(obs, param, Rs, VPD_kPa, theta) {
    obs - jarvis(param, Rs, VPD_kPa, theta)
  }

param_init <- list(g_ref = 474, a1 = 9, a2 = 0.01, m = 0.6)

nls_Tr <-
  data_daily %>% 
  mutate(VPD_60m_kPa = 0.1*VPD_60m,
         g_bulk = Tr*Pa_atm_kPa / (VPD_60m_kPa)) %>% 
  filter(date >= date_obs_head & date <= date_obs_tail) %$%
  nls.lm(par = param_init, fn = resid, obs = g_bulk, Rs = Rs_in,
         VPD_kPa = VPD_60m_kPa, theta = SWC_120_La1) %>% 
  summary()


## estimate transpiration time series using the Jarvis-type model
data_daily %<>% 
  mutate(VPD_60m_kPa = 0.1*VPD_60m,
         Tr_calc = jarvis(as.list(coef(nls_Tr)[1:4, 1]),
                          Rs_in, VPD_60m_kPa, SWC_120_La1) *
           VPD_60m_kPa / Pa_atm_kPa)

## validate output values
lm_Tr <-
  data_daily %>% 
  filter(date >= date_obs_head & date <= date_obs_tail) %$%
  lm(Tr ~ Tr_calc) %>% 
  summary()

slp_Tr <- coef(lm_Tr)[2, 1] %>% round(digits = 2)
int_Tr <- coef(lm_Tr)[1, 1] %>% round(digits = 2)
R2_Tr <- lm_Tr$adj.r.squared %>% round(digits = 2)

RMSE_Tr <- 
  data_daily %>% 
  filter(date >= date_obs_head & date <= date_obs_tail) %>%
  mutate(cost = (Tr - Tr_calc)^2) %$% 
  mean(cost) %>% 
  sqrt(.)


## draw a scatter plot
p_Tr_obs_calc <-
  data_daily %>% 
  filter(date >= date_obs_head & date <= date_obs_tail) %>%
  ggplot()+
  theme_classic()+
  theme(axis.title = element_text(size = 14),
        axis.text.x = element_text(size = 12, colour = "black"),
        axis.text.y = element_text(size = 12, colour = "black"),
        axis.ticks = element_line(colour = "black"),
        axis.ticks.length = unit(3, "mm"))+
  labs(x = bquote( italic("T")["r, modeled"]~(mm~day^{-1}) ),
       y = bquote( italic("T")["r, observed"]~(mm~day^{-1}) ))+
  coord_equal()+
  scale_x_continuous(limits = c(0, 5.7), breaks = seq(0, 5),
                     labels = c(0, "", 2, "", 4, ""), expand = expansion())+
  scale_y_continuous(limits = c(0, 5.7), breaks = seq(0, 5),
                     labels = c(0, "", 2, "", 4, ""), expand = expansion())+
  geom_point(aes(Tr_calc, Tr), size = 2, col = "skyblue",
             alpha = 0.3)+
  geom_abline(slope = slp_Tr, intercept = int_Tr,
              col = "gray40", lwd = 1.2, alpha = 0.8)+
  geom_abline(slope = 1, intercept = 0, col = "black", lty = "dashed")+
  annotate("text", x = 0.3, y = 5.4,
           label = paste0("italic(y) ==", slp_Tr, "*italic(x)", int_Tr),
           parse = TRUE, col = "black", size = 4, hjust = 0)+
  annotate("text", x = 2.2, y = 5.45, label = "0",
           col = "black", size = 4, hjust = 0, vjust = 0.52)+
  annotate("text", x = 0.3, y = 5.0,
           label = paste0("italic(R)^2 ==", R2_Tr),
           parse = TRUE, col = "black", size = 4, hjust = 0)

p_Tr_obs_calc

# ggsave(file = "./LHP_Jarvis_Tr_1by1_ver01.pdf",
#        plot = p_Tr_obs_calc, width = 100, height = 100,
#        units = "mm", device = cairo_pdf)


# total loss for each soil water storage ----------------------------------

## calculate binned medians of observed transpiration and estimate drainage
W_sat <- theta_max*1.2*1e3
x_rW <- seq(0.65, 1, by = 0.0001) %>% round(digits = 4)
y_Dr <- K_sat_K04 * x_rW^(2*b_C78+3)

df_loss <-
  data_daily %>% 
  filter(date >= date_obs_head & date <= date_obs_tail) %>% 
  mutate(rW_120 = SWC_120_La1*1.2*1e3 / W_sat,
         rW_120 = ifelse(rW_120 > 1, 1, rW_120),
         bin_rW = cut_width(rW_120, width = 0.05)) %>% 
  group_by(bin_rW) %>% 
  summarise(Tr_med = median(Tr),
            Tr_Q1 = quantile(Tr, 0.25),
            Tr_Q3 = quantile(Tr, 0.75)) %>% 
  mutate(rW_mid = seq(0.65, 1, by = 0.05) %>% round(digits = 3)) %>% 
  select(rW_mid, Tr_med, Tr_Q1, Tr_Q3) %>% 
  as.data.frame() %>% 
  merge.data.frame(data.frame(rW = x_rW), ., by.x = "rW", by.y = "rW_mid",
                   all = TRUE) %>% 
  mutate(Tr_med_intpl = na.approx(Tr_med),
         Dr = y_Dr,
         loss = Tr_med_intpl + Dr,
         ratio_Dr = Dr / Tr_med_intpl)


## draw a graph
TrDr_max <- 40
ratio_Dr_max <- 12

p_loss <-
  df_loss %>% 
  mutate(ratio_Dr_scaled = ratio_Dr/ratio_Dr_max * TrDr_max) %>% 
  ggplot()+
  theme_classic()+
  theme(axis.title = element_text(size = 14),
        axis.text.x = element_text(size = 12, colour = "black"),
        axis.text.y = element_text(size = 12, colour = "black"),
        axis.ticks = element_line(colour = "black"),
        axis.ticks.length = unit(3, "mm"))+
  labs(x = bquote( italic(w)*"/"*(italic("\u03B7")*italic(Z)[r]) ),
       y = bquote( Water~loss~rate~(mm~day^{-1}) ))+
  scale_x_continuous(limits = c(0.65, 1), breaks = seq(0.65, 1, by = 0.05),
                     labels = c("", 0.7, "", 0.8, "", 0.9, "", 1),
                     expand = expansion())+
  scale_y_continuous(limits = c(0, TrDr_max), breaks = seq(0, 40, by = 10),
                     labels = c(0, "", 20, "", 40),
                     expand = expansion(),
                     sec.axis = sec_axis(~ . / TrDr_max * ratio_Dr_max,
                                         breaks = seq(0, 10, by = 2.5),
                                         labels = c(0, "", 5, "", 10),
                                         name = bquote(italic(D)[r]/
                                                         italic("T")[r])))+
  geom_line(aes(rW, Tr_med_intpl), col = "skyblue", lwd = 0.8, alpha = 1,
            lty = "dashed")+
  geom_point(aes(rW, Tr_med), col = "skyblue", size = 2, alpha = 1)+
  geom_line(aes(rW, Dr), col = "plum", lwd = 0.8, alpha = 0.8)+
  geom_line(aes(rW, ratio_Dr_scaled), col = "black", lwd = 1, alpha = 0.6,
            lty = "dotted")

p_loss

# ggsave(file = "./LHP_drainage_ratio_ver01.pdf",
#        plot = p_loss, width = 190, height = 100,
#        units = "mm", device = cairo_pdf)


# determine function shape for ratio_Tr -------------------------------

## ratio_Tr: contribution of shallow-root water uptake to transpiration
## define sigmoid function
f_sigmoid <- function(param, r) {
  0.55 / (1 + exp(-param$a*(r-param$b)))
}

resid <- function(obs, param, r) {
  obs - f_sigmoid(param, r)
}

param_init <- list(a = 70, b = 0.7)
ulim_rW <- 0.725

## calculate binned medians of observed ratio_Tr
df_ratio_Tr_med_obs <-
  data_daily %>%
  mutate(dwdt = lead(W_120_La1) - W_120_La1,
         rW = SWC_120_La1/theta_max,
         Ic = ifelse(PPT >= 0.90 & PPT < 3.91,
                     0.13*PPT + 0.78, PPT),
         Ic = ifelse(PPT >= 3.91, 0.084*PPT + 0.96, Ic),
         ratio = (PPT - Ic - dwdt)/Tr) %>%
  filter(date >= date_obs_head & date <= date_obs_tail &
           ratio >= 0 & ratio <= 1 & rW <= ulim_rW) %>%
  mutate(bin_rW = cut_width(rW, width = 0.0125)) %>% 
  group_by(bin_rW) %>% 
  summarise(ratio_med = median(ratio),
            ratio_Q1 = quantile(ratio, 0.25),
            ratio_Q3 = quantile(ratio, 0.75)) %>% 
  mutate(rW_mid = seq(0.650, 0.725, by = 0.0125) %>% round(digits = 4)) %>% 
  select(rW_mid, ratio_med, ratio_Q1, ratio_Q3) %>% 
  as.data.frame()

## fit parameters
nls_ratio_Tr <-
  df_ratio_Tr_med_obs %$%
  nls.lm(par = param_init, fn = resid, obs = ratio_med, r = rW_mid) %>% 
  summary()


## draw a graph
df_sigmoid_fig <-
  data.frame(xxx = seq(0.64, ulim_rW, length.out = 1000)) %>% 
  mutate(yyy = f_sigmoid(as.list(coef(nls_ratio_Tr)[, 1]), xxx))

col_fit <- "tan4"

p_ratio_Tr_obs <-
  data_daily %>%
  mutate(dwdt = lead(W_120_La1) - W_120_La1,
         rW = SWC_120_La1/theta_max,
         Ic = ifelse(PPT >= 0.90 & PPT < 3.91,
                     0.13*PPT + 0.78, PPT),
         Ic = ifelse(PPT >= 3.91, 0.084*PPT + 0.96, Ic),
         ratio = (PPT - Ic - dwdt)/Tr) %>%
  filter(date >= date_obs_head & date <= date_obs_tail &
           ratio >= 0 & ratio <= 1 & rW <= ulim_rW) %>%
  mutate(xxx = seq(0.64, ulim_rW, length.out = nrow(.)),
         yyy = f_sigmoid(as.list(coef(nls_ratio_Tr)[, 1]), xxx)) %>%
  ggplot()+
  theme_classic()+
  theme(axis.title = element_text(size = 18),
        axis.text.x = element_text(size = 16, colour = "black"),
        axis.text.y = element_text(size = 16, colour = "black"),
        axis.ticks = element_line(colour = "black"),
        axis.ticks.length = unit(3, "mm"))+
  labs(x = bquote( italic(w) / (italic("\u03B7")*italic(Z)[r]) ),
       y = bquote( italic(r) ))+
  scale_x_continuous(limits = c(0.64, 0.727),
                     breaks = seq(0.65, 0.725, by = 0.025),
                     labels = c(0.65, "", 0.70, ""), expand = expansion())+
  scale_y_continuous(limits = c(0, 1.025),
                     breaks = seq(0, 1, by = 0.25),
                     labels = c(0, "", 0.5, "", 1), expand = expansion())+
  geom_point(aes(rW, ratio), col = "gray70", size = 2, shape = 4)+
  geom_point(data = df_ratio_Tr_med_obs, aes(rW_mid, ratio_med),
             col = col_fit, size = 4)+
  geom_errorbar(data = df_ratio_Tr_med_obs,
                aes(rW_mid, ymin = ratio_Q1, ymax = ratio_Q3), col = col_fit,
                lwd = 1, width = 0.0025)+
  geom_line(data = df_sigmoid_fig, aes(xxx, yyy), col = col_fit, lwd = 1)+
  geom_hline(yintercept = 0.55, col = "tan2", lwd = 0.5, lty = "dashed")+
  geom_hline(yintercept = 1, col = "tan", lwd = 0.5, lty = "dotted")


p_ratio_Tr_obs

# ggsave(file = "./LHP_ratioTr_fitting_ver02.pdf",
#        plot = p_ratio_Tr_obs, width = 190, height = 100,
#        units = "mm", device = cairo_pdf)


# hydraulic balance model -------------------------------------------------

## note that theta_max is the maximum observed value in the entire period,
## and theta_init is the first observed value in the entire period
model_W <- function(vctr_PPT, vctr_Rs, vctr_D_kPa, vctr_W = NULL,
                    vctr_Tr = NULL, K_sat_opt = 35.6, b_opt = 4.6,
                    g_ref = 473.86, Rs_max = 24.24, a1 = 5.578, m = 0.7540,
                    theta_max = 0.3602747, a2 = 0.08782, r1 = 59.924,
                    r2 = 0.676, depth_root = 1.2, dt = 1, Pa_atm_kPa = 101.325,
                    theta_init = 0.3124167, digit_calib = 1,
                    vctr_ratio_Tr = 1, modify_ratio_Tr = FALSE,
                    label_err = -9999) {
  
  PPT <- vctr_PPT
  Rs <- vctr_Rs
  D <- vctr_D_kPa
  ratio_Tr <- vctr_ratio_Tr
  
  if(length(ratio_Tr) == 1) {
    ratio_Tr <- rep(ratio_Tr, length(PPT))
  }
  
  W_max <- theta_max*depth_root*1e3
  W_init <- theta_init*depth_root*1e3
  
  ## estimate water balance components
  W <- NULL
  theta <- NULL
  pond <- NULL
  Ic <- NULL
  Tr <- NULL
  Dr <- NULL
  input <- NULL
  
  W[1] <- W_init
  theta[1] <- W[1]/(depth_root*1e3)
  pond[1] <- 0
  
  for(k in 1:length(PPT)) {
    Ic[k] <-
      ifelse(PPT[k] >= 0.90 & PPT[k] < 3.91, 0.13*PPT[k] + 0.78, PPT[k])
    Ic[k] <- ifelse(PPT[k] >= 3.91, 0.084*PPT[k] + 0.96, Ic[k])
    
    if(!is.null(vctr_Tr)) {
      Tr[k] <- vctr_Tr[k]
    } else {
      Tr[k] <-
        g_ref * Rs[k]*(Rs_max + a1)/(Rs_max*(Rs[k] + a1)) *
        (1-m*log(D[k])) *
        theta[k]*(theta_max + a2)/(theta_max*(theta[k] + a2)) *
        D[k] / Pa_atm_kPa
    }
    
    if(modify_ratio_Tr) {
      ratio_Tr[k] <- f_sigmoid(list(a = r1, b = r2), W[k]/W_max)
    }
    
    Dr[k] <- K_sat_opt*(W[k]/W_max)^(2*b_opt+3)
    input[k] <- PPT[k] + pond[k]/dt - Ic[k]
    
    if(k == length(PPT)) next
    if(input[k] <= K_sat_opt) {
      W[k+1] <- min(W[k] + (input[k] - ratio_Tr[k]*Tr[k] - Dr[k])*dt, W_max)
      theta[k+1] <- W[k+1]/(depth_root*1e3)
      pond[k+1] <- 0
    } else {
      W[k+1] <- min(W[k] + (K_sat_opt - ratio_Tr[k]*Tr[k] - Dr[k])*dt, W_max)
      theta[k+1] <- W[k+1]/(depth_root*1e3)
      pond[k+1] <- (input[k] - K_sat_opt)*dt
    }
  }
  ## make output data frame
  data.frame(W_calc = W,
             PPT = PPT,
             Ic = Ic,
             Tr = Tr,
             Dr = Dr,
             ratio_Tr = ratio_Tr,
             pond = pond) %>% 
    return()
}


## linear loss model
model_W_linear <- function(vctr_PPT, L_max = 130.446,
                           theta_max = 0.3602747, depth_root = 1.2,
                           dt = 1, theta_init = 0.3124167, digit_calib = 1,
                           label_err = -9999) {
  
  PPT <- vctr_PPT
  
  W_max <- theta_max*depth_root*1e3
  W_init <- theta_init*depth_root*1e3
  
  ## estimate water balance components
  W <- NULL
  theta <- NULL
  L <- NULL
  input <- NULL
  
  W[1] <- W_init
  theta[1] <- W[1]/(depth_root*1e3)
  
  Ic <- ifelse(PPT >= 0.90 & PPT < 3.91, 0.13*PPT + 0.78, PPT)
  Ic <- ifelse(PPT >= 3.91, 0.084*PPT + 0.96, Ic)
  
  for(k in 1:length(PPT)) {
    L[k] <- L_max * W[k]/W_max
    
    if(k == length(PPT)) next
    
    W[k+1] <- min((W[k] + PPT[k] - Ic[k] - L[k]) * dt, W_max)
    theta[k+1] <- W[k+1]/(depth_root*1e3)
  }
  ## make output data frame
  data.frame(W_calc = W,
             PPT = PPT,
             Ic = Ic,
             L = L) %>% 
    return()
}


# calculate water balance for each loss model -----------------------------

## initial conditions
theta_init <-
  data_daily %>%
  filter(date == date_obs_head) %>%
  pull(SWC_120_La1)

theta_init_all <-
  data_daily %>% 
  filter(QC_SWC_120_La1 >= 0.5) %>% 
  pull(SWC_120_La1) %>% 
  mean()

## make input vectors
data_daily %>% 
  mutate(W = ifelse(QC_SWC_120_La1 >= 0.5, W_120_La1, -9999)) %>%
  filter(date >= date_obs_head & date <= date_obs_tail) %>% {
    .$PPT ->> vctr_PPT
    .$Rs_in ->> vctr_Rs
    .$VPD_60m_kPa ->> vctr_D
    .$W ->> vctr_W_obs
    .$Tr ->> Tr_obs
  }


## shallow water only
df_balance_obsTr_sh <-
  model_W(vctr_PPT, vctr_Rs, vctr_D, vctr_Tr = Tr_obs,
          K_sat_opt = K_sat_K04, b_opt = b_C78, 
          theta_max = theta_max,
          vctr_ratio_Tr = 1, theta_init = theta_init,
          modify_ratio_Tr = FALSE)

RMSE_sh <-
  df_balance_obsTr_sh %>% 
  mutate(W_obs = vctr_W_obs) %>% 
  filter(W_obs > -9999) %>% 
  mutate(SE = (W_obs - W_calc)^2) %>% 
  pull(SE) %>% 
  mean() %>% 
  sqrt()

lm_balance_sh <-
  df_balance_obsTr_sh %>% 
  mutate(W_obs = vctr_W_obs) %>% 
  filter(W_obs > -9999) %$% 
  lm(W_calc ~ W_obs) %>% 
  summary()

slp_sh <- coef(lm_balance_sh)[2, 1] %>% round(digits = 2)
int_sh <- coef(lm_balance_sh)[1, 1] %>% round(digits = 2)
R2_sh <- lm_balance_sh$adj.r.squared %>% round(digits = 2)


## fixed shallow water ratio
ratio_Tr_fx <- 0.55

df_balance_obsTr_fx <-
  model_W(vctr_PPT, vctr_Rs, vctr_D, vctr_Tr = Tr_obs,
          K_sat_opt = K_sat_K04, b_opt = b_C78, 
          theta_max = theta_max,
          vctr_ratio_Tr = ratio_Tr_fx, theta_init = theta_init,
          modify_ratio_Tr = FALSE)

RMSE_fx <-
  df_balance_obsTr_fx %>% 
  mutate(W_obs = vctr_W_obs) %>% 
  filter(W_obs > -9999) %>% 
  mutate(SE = (W_obs - W_calc)^2) %>% 
  pull(SE) %>% 
  mean() %>% 
  sqrt()

lm_balance_fx <-
  df_balance_obsTr_fx %>% 
  mutate(W_obs = vctr_W_obs) %>% 
  filter(W_obs > -9999) %$% 
  lm(W_calc ~ W_obs) %>% 
  summary()

slp_fx <- coef(lm_balance_fx)[2, 1] %>% round(digits = 2)
int_fx <- coef(lm_balance_fx)[1, 1] %>% round(digits = 2)
R2_fx <- lm_balance_fx$adj.r.squared %>% round(digits = 2)


## non-stationary shallow water ratio
df_balance_obsTr_ns <-
  model_W(vctr_PPT, vctr_Rs, vctr_D, vctr_Tr = Tr_obs,
          K_sat_opt = K_sat_K04, b_opt = b_C78, 
          theta_max = theta_max, theta_init = theta_init,
          modify_ratio_Tr = TRUE)

RMSE_ns <-
  df_balance_obsTr_ns %>% 
  mutate(W_obs = vctr_W_obs) %>% 
  filter(W_obs > -9999) %>% 
  mutate(SE = (W_obs - W_calc)^2) %>% 
  pull(SE) %>% 
  mean() %>% 
  sqrt()

lm_balance_ns <-
  df_balance_obsTr_ns %>% 
  mutate(W_obs = vctr_W_obs) %>% 
  filter(W_obs > -9999) %$% 
  lm(W_calc ~ W_obs) %>% 
  summary()

slp_ns <- coef(lm_balance_ns)[2, 1] %>% round(digits = 2)
int_ns <- coef(lm_balance_ns)[1, 1] %>% round(digits = 2)
R2_ns <- lm_balance_ns$adj.r.squared %>% round(digits = 2)


# draw calculated time series --------------------------------------------

size_axis_title <- 14
size_axis_text <- 12
size_anno <- 3
size_anno_fignum <- 4
size_date <- 4
size_point_ts <- 2
alpha_point_ts <- 0.2
size_eq <- 2.25
size_point_1by1 <- 0.8


## for x-axis label
df_label <-
  data.frame(date = c(ymd("2013/09/05", tz = timezone),
                      ymd("2014/07/01", tz = timezone),
                      ymd("2015/07/01", tz = timezone),
                      ymd("2016/07/01", tz = timezone))) %>% 
  mutate(yval = 0,
         label_yr = seq(2013, 2016))


p_W_ts_calib <-
  df_balance_obsTr_ns %>% 
  mutate(date = vctr_date_obs,
         W_obs = ifelse(vctr_W_obs == -9999, NA, vctr_W_obs),
         W_calc_sh = df_balance_obsTr_sh$W_calc,
         W_calc_fx = df_balance_obsTr_fx$W_calc) %>% 
  ggplot()+
  theme_classic()+
  theme(axis.title = element_text(size = size_axis_title),
        axis.text.x = element_blank(),
        axis.text.y = element_text(size = size_axis_text, colour = "black"),
        axis.ticks = element_line(colour = "black"),
        axis.ticks.length = unit(3, "mm"))+
  labs(x = "",
       y = bquote( italic(w)~(mm) ))+
  coord_cartesian(clip = "off")+
  scale_x_datetime(date_breaks = "1 year", date_labels = "%Y",
                   expand = expansion())+
  scale_y_continuous(limits = c(0, 450), breaks = seq(0, 400, by = 100),
                     labels = c(0, "", 200, "", 400),
                     expand = expansion())+
  geom_point(aes(date, W_obs), col = "transparent", fill = "black",
             size = size_point_ts, shape = 21, alpha = alpha_point_ts)+
  geom_line(aes(date, W_calc_sh), col = "tan", lwd = 0.7, lty = "dotted",
            alpha = 0.8)+
  geom_line(aes(date, W_calc_fx), col = "tan2", lwd = 1.2, alpha = 0.8)+
  geom_line(aes(date, W_calc), col = "tan4", lwd = 0.8, alpha = 0.8,
            lty = "longdash")+
  geom_text(data = df_label, aes(date, yval, label = label_yr),
            size = size_date, col = "black", vjust = 1.6)+
  annotate("text", x = date_obs_head, y = Inf, label = "(a)",
           col = "black", size = size_anno_fignum, hjust = -0.2, vjust = 1)+
  annotate("point", x = ymd("2016/11/22", tz = timezone), y = 120,
           col = "transparent", fill = "black",
           size = size_point_ts, shape = 21, alpha = alpha_point_ts)+
  annotate("segment", x = ymd("2016/11/01", tz = timezone),
           xend = ymd("2016/12/15", tz = timezone), y = 90,
           col = "tan", lwd = 0.7, alpha = 0.8, lty = "dotted")+
  annotate("segment", x = ymd("2016/11/01", tz = timezone),
           xend = ymd("2016/12/15", tz = timezone), y = 60,
           col = "tan2", lwd = 0.8, alpha = 0.8)+
  annotate("segment", x = ymd("2016/11/01", tz = timezone),
           xend = ymd("2016/12/15", tz = timezone), y = 30,
           col = "tan4", lwd = 0.6, alpha = 0.8, lty = "dashed")+
  annotate("text", x = ymd("2016/12/25", tz = timezone), y = 120,
           label = "Observed", col = "black", size = size_anno, hjust = 0,
           vjust = 0.4)+
  annotate("text", x = ymd("2016/12/25", tz = timezone), y = 90,
           label = "Case 1", col = "black", size = size_anno, hjust = 0,
           vjust = 0.4)+
  annotate("text", x = ymd("2016/12/25", tz = timezone), y = 60,
           label = "Case 2", col = "black", size = size_anno, hjust = 0,
           vjust = 0.4)+
  annotate("text", x = ymd("2016/12/25", tz = timezone), y = 30,
           label = "Case 3", col = "black", size = size_anno, hjust = 0,
           vjust = 0.4)


## scatter plots for each loss function model
p_1by1_balance_obsTr_sh <-
  df_balance_obsTr_sh %>% 
  mutate(W_obs = ifelse(vctr_W_obs == -9999, NA, vctr_W_obs)) %>% 
  ggplot()+
  theme_classic()+
  theme(axis.title = element_text(size = size_axis_title),
        axis.text.x = element_text(size = size_axis_text, colour = "black"),
        axis.text.y = element_text(size = size_axis_text, colour = "black"),
        axis.ticks = element_line(colour = "black"),
        axis.ticks.length = unit(3, "mm"))+
  labs(x = bquote( italic(w)[observed]~(mm) ),
       y = bquote( italic(w)[modeled]~(mm) ))+
  coord_fixed()+
  scale_x_continuous(limits = c(0, 450), breaks = seq(0, 400, by = 100),
                     labels = c(0, "", 200, "", 400),
                     expand = expansion())+
  scale_y_continuous(limits = c(0, 450), breaks = seq(0, 400, by = 100),
                     labels = c(0, "", 200, "", 400),
                     expand = expansion())+
  geom_point(aes(W_obs, W_calc), col = "tan", size = size_point_1by1,
             alpha = 0.3)+
  geom_abline(slope = 1, intercept = 0, col = "gray30", lwd = 0.5, alpha = 0.8,
              lty = "dashed")+
  geom_abline(slope = coef(lm_balance_sh)[2, 1],
              intercept = coef(lm_balance_sh)[1, 1],
              col = "black", lwd = 0.8, alpha = 0.8)+
  annotate("text", x = -Inf, y = Inf, label = "(b) Case 1",
           col = "black", size = size_anno_fignum, hjust = -0.05, vjust = 1)+
  annotate("text", x = 20, y = 350,
           label = paste0("italic(y) ==", slp_sh, "*italic(x)", int_sh),
           parse = TRUE, col = "black", size = size_eq, hjust = 0)+
  annotate("text", x = 20, y = 310,
           label = paste0("italic(R)^2 ==", R2_sh),
           parse = TRUE, col = "black", size = size_eq, hjust = 0)



p_1by1_balance_obsTr_fx <-
  df_balance_obsTr_fx %>% 
  mutate(W_obs = ifelse(vctr_W_obs == -9999, NA, vctr_W_obs)) %>% 
  ggplot()+
  theme_classic()+
  theme(axis.title = element_text(size = size_axis_title),
        axis.text.x = element_text(size = size_axis_text, colour = "black"),
        axis.text.y = element_blank(),
        axis.ticks = element_line(colour = "black"),
        axis.ticks.length = unit(3, "mm"))+
  labs(x = bquote( italic(w)[observed]~(mm) ),
       y = "")+
  coord_fixed()+
  scale_x_continuous(limits = c(0, 450), breaks = seq(0, 400, by = 100),
                     labels = c(0, "", 200, "", 400),
                     expand = expansion())+
  scale_y_continuous(limits = c(0, 450), breaks = seq(0, 400, by = 100),
                     labels = c(0, "", 200, "", 400),
                     expand = expansion())+
  geom_point(aes(W_obs, W_calc), col = "tan2", size = size_point_1by1,
             alpha = 0.3)+
  geom_abline(slope = 1, intercept = 0, col = "gray30", lwd = 0.5, alpha = 0.8,
              lty = "dashed")+
  geom_abline(slope = coef(lm_balance_fx)[2, 1],
              intercept = coef(lm_balance_fx)[1, 1],
              col = "black", lwd = 0.8, alpha = 0.8)+
  annotate("text", x = -Inf, y = Inf, label = "(c) Case 2",
           col = "black", size = size_anno_fignum, hjust = -0.05, vjust = 1)+
  annotate("text", x = 20, y = 350,
           label = paste0("italic(y) ==", slp_fx, "*italic(x)", int_fx),
           parse = TRUE, col = "black", size = size_eq, hjust = 0)+
  annotate("text", x = 20, y = 310,
           label = paste0("italic(R)^2 ==", R2_fx),
           parse = TRUE, col = "black", size = size_eq, hjust = 0)


p_1by1_balance_obsTr_ns <-
  df_balance_obsTr_ns %>% 
  mutate(W_obs = ifelse(vctr_W_obs == -9999, NA, vctr_W_obs)) %>% 
  ggplot()+
  theme_classic()+
  theme(axis.title = element_text(size = size_axis_title),
        axis.text.x = element_text(size = size_axis_text, colour = "black"),
        axis.text.y = element_blank(),
        axis.ticks = element_line(colour = "black"),
        axis.ticks.length = unit(3, "mm"))+
  labs(x = bquote( italic(w)[observed]~(mm) ),
       y = "")+
  coord_fixed()+
  scale_x_continuous(limits = c(0, 450), breaks = seq(0, 400, by = 100),
                     labels = c(0, "", 200, "", 400),
                     expand = expansion())+
  scale_y_continuous(limits = c(0, 450), breaks = seq(0, 400, by = 100),
                     labels = c(0, "", 200, "", 400),
                     expand = expansion())+
  geom_point(aes(W_obs, W_calc), col = "tan4", size = size_point_1by1,
             alpha = 0.3)+
  geom_abline(slope = 1, intercept = 0, col = "gray30", lwd = 0.5, alpha = 0.8,
              lty = "dashed")+
  geom_abline(slope = coef(lm_balance_ns)[2, 1],
              intercept = coef(lm_balance_ns)[1, 1],
              col = "black", lwd = 0.8, alpha = 0.8)+
  annotate("text", x = -Inf, y = Inf, label = "(d) Case 3",
           col = "black", size = size_anno_fignum, hjust = -0.05, vjust = 1)+
  annotate("text", x = 20, y = 350,
           label = paste0("italic(y) ==", slp_ns, "*italic(x)+", int_ns),
           parse = TRUE, col = "black", size = size_eq, hjust = 0)+
  annotate("text", x = 20, y = 310,
           label = paste0("italic(R)^2 ==", R2_ns),
           parse = TRUE, col = "black", size = size_eq, hjust = 0)


p_balance_ts_1by1 <-
  p_W_ts_calib /
  (p_1by1_balance_obsTr_sh | p_1by1_balance_obsTr_fx |
     p_1by1_balance_obsTr_ns)+
  plot_layout(heights = c(3, 2))

# p_balance_ts_1by1


# generate artificial precipitation ---------------------------------------

## calculate precipitation characteristics
vctr_dep_PPT <- NULL
vctr_freq_PPT <- NULL

for (i_yr in 2009:2019) {
  for (i_mon in 1:12) {
    if(i_yr == 2009 & i_mon <= 11) next
    if(i_yr == 2019 & i_mon == 12) next
    if(mod(i_mon, 2) == 1) next
    
    if(i_mon == 12) {
      stats_PPT <-
        data_daily %>% 
        filter((year == i_yr & month == i_mon) |
                 (year == i_yr+1 & month == 1)) %>% 
        pull(PPT) %>% 
        calc_precip_stats()
    } else {
      stats_PPT <-
        data_daily %>% 
        filter(year == i_yr & between(month, i_mon, i_mon+1)) %>% 
        pull(PPT) %>% 
        calc_precip_stats()
    }
    
    vctr_freq_PPT <- c(vctr_freq_PPT, stats_PPT[1])
    vctr_dep_PPT <- c(vctr_dep_PPT, stats_PPT[2])
  }
}


## make white-noise precipitation (wettest and driest features)
df_stats_PPT_season <-
  data.frame(date = seq(ymd("2010/01/01", tz = timezone),
                        ymd("2019/11/01", tz = timezone), by = "2 months"),
             dep = vctr_dep_PPT,
             freq = vctr_freq_PPT) %>%
  mutate(mon = month(date),
         mon_label = case_when(mon == 1 ~ "DJ",
                               mon == 3 ~ "FM",
                               mon == 5 ~ "AM",
                               mon == 7 ~ "JJ",
                               mon == 9 ~ "AS",
                               mon == 11 ~ "ON"),
         mon_label = factor(mon_label,
                            levels = c("DJ", "FM", "AM", "JJ", "AS",
                                       "ON"))) %>% 
  group_by(mon_label) %>% 
  summarise(freq_avg = mean(freq),
            dep_avg = mean(dep)) %>% 
  as.data.frame()


PPT_daily_wht_wet <-
  generate_precip(df_stats_PPT_season$freq_avg[1],
                  df_stats_PPT_season$dep_avg[1],
                  n = length(PPT_daily))

PPT_daily_wht_dry <-
  generate_precip(df_stats_PPT_season$freq_avg[2],
                  df_stats_PPT_season$dep_avg[2],
                  n = length(PPT_daily))


## make white-noise precipitation (averaged feature)
PPT_daily_wht_avg <-
  generate_precip(mean(df_stats_PPT_season$freq_avg),
                  mean(df_stats_PPT_season$dep_avg),
                  n = length(PPT_daily))


## make ENSO & seasonality-added artificial precipitation
vctr_n_days <-
  data_daily %>% 
  group_by(year, month) %>% 
  summarise(n_day = n(), .groups = "drop_last") %>% 
  as.data.frame() %>%
  mutate(n_cum = n_day + lag(n_day)) %>% 
  slice(3:(nrow(.)-1)) %>% 
  filter(mod(month, 2) == 1) %>% 
  pull(n_cum)

## for 2009/11 and 2019/12
data_daily %>% 
  filter(year == 2009 & month >= 11) %$% 
  calc_precip_stats(PPT) %>%  {
    .[1] ->> freq_PPT_200911
    .[2] ->> dep_PPT_200911
  }

data_daily %>% 
  filter(year == 2019 & month >= 11) %$% 
  calc_precip_stats(PPT) %>%  {
    .[1] ->> freq_PPT_201912
    .[2] ->> dep_PPT_201912
  }

PPT_daily_ENSO <- generate_precip(freq_PPT_200911, dep_PPT_200911, n = 30)

for (i in 1:length(vctr_n_days)) {
  PPT_daily_ENSO <-
    generate_precip(vctr_freq_PPT[i], vctr_dep_PPT[i], vctr_n_days[i],
                    seed = i) %>% 
    c(PPT_daily_ENSO, .)
}

PPT_daily_ENSO <-
  generate_precip(freq_PPT_201912, dep_PPT_201912, n = 31) %>% 
  c(PPT_daily_ENSO, .)


## make seasonality-added artificial precipitation
## for 2009/11
PPT_daily_season <-
  generate_precip(df_stats_PPT_season$freq_avg[6],
                  df_stats_PPT_season$dep_avg[6], n = 30)

for (i in 1:length(vctr_n_days)) {
  PPT_daily_season <-
    generate_precip(df_stats_PPT_season$freq_avg[ifelse(mod(i, 6) > 0,
                                                        mod(i, 6), 6)],
                    df_stats_PPT_season$dep_avg[ifelse(mod(i, 6) > 0,
                                                       mod(i, 6), 6)],
                    vctr_n_days[i], seed = i) %>% 
    c(PPT_daily_season, .)
}

## for 2019/12
PPT_daily_season <-
  generate_precip(df_stats_PPT_season$freq_avg[1],
                  df_stats_PPT_season$dep_avg[1], n = 31) %>% 
  c(PPT_daily_season, .)


## gather generated time series
df_PPT_set <-
  data.frame(ob = PPT_daily,
             av = PPT_daily_wht_avg,
             wt = PPT_daily_wht_wet,
             dr = PPT_daily_wht_dry,
             ss = PPT_daily_season,
             es = PPT_daily_ENSO)


# generate high-pass filtered meteorological factors ----------------------

## set cut-off days
days_cutoff_ENSO <- 900
days_cutoff_season <- 300

## filter solar radiation time series
Rs_daily <- data_daily %>% pull(Rs_in)

Rs_daily_hp_avg0_ENSO <-
  Rs_daily %>% filter_hp(., 1/86400, 24*days_cutoff_ENSO)
Rs_daily_hp_ENSO <- Rs_daily_hp_avg0_ENSO + mean(Rs_daily)
Rs_daily_hp_ENSO[Rs_daily_hp_ENSO < 0] <- 0

Rs_daily_hp_avg0_season <-
  Rs_daily %>% filter_hp(., 1/86400, 24*days_cutoff_season)
Rs_daily_hp_season <- Rs_daily_hp_avg0_season + mean(Rs_daily)
Rs_daily_hp_season[Rs_daily_hp_season < 0] <- 0


## filter VPD time series
VPD_daily <- data_daily %>% pull(VPD_60m_kPa)

VPD_daily_hp_avg0_ENSO <-
  VPD_daily %>% filter_hp(., 1/86400, 24*days_cutoff_ENSO)
VPD_daily_hp_ENSO <- VPD_daily_hp_avg0_ENSO + mean(VPD_daily)
VPD_daily_hp_ENSO[VPD_daily_hp_ENSO < 0] <- 1e-6

VPD_daily_hp_avg0_season <-
  VPD_daily %>% filter_hp(., 1/86400, 24*days_cutoff_season)
VPD_daily_hp_season <- VPD_daily_hp_avg0_season + mean(VPD_daily)
VPD_daily_hp_season[VPD_daily_hp_season < 0] <- 1e-6


## gather filtered time series
df_Rs_set <-
  data.frame(ob = Rs_daily,
             eo = Rs_daily_hp_ENSO,
             so = Rs_daily_hp_season)

df_VPD_set <-
  data.frame(ob = VPD_daily,
             eo = VPD_daily_hp_ENSO,
             so = VPD_daily_hp_season)


# numerical experiments for memory ----------------------------------------

## parameter fitting results
df_para_opt <-
  data.frame(model = c("sh", "fx", "ns"),
             K_sat = c(K_sat_K04, K_sat_K04, K_sat_K04),
             b = c(b_C78, b_C78, b_C78),
             ratio_Tr = c(1, ratio_Tr_fx, -9999),
             RMSE = c(RMSE_sh, RMSE_fx, RMSE_ns))

## observed memory
memory_obs <- calc_memory(vctr_W_obs, t_step_hr = 24)

## linear loss model
## determine L_max by observed time series
L_max_obs <-
  data_daily %>% 
  mutate(dW = W_120_La1 - lag(W_120_La1),
         Ic = ifelse(PPT >= 0.90 & PPT < 3.91, 0.13*PPT + 0.78, PPT),
         Ic = ifelse(PPT >= 3.91, 0.084*PPT + 0.96, Ic),
         L = PPT - Ic - dW) %>% 
  filter(date >= date_obs_head & date <= date_obs_tail &
           QC_SWC_120_La1 >= 0.5) %>% 
  pull(L) %>% 
  quantile(., probs = 0.99) %>% 
  as.numeric()

## calculate theoretical memory
memory_DM88 <- theta_max*1.2*1e3/L_max_obs*24

## estimate memory using different precipitation time series
vctr_name_PPT <- names(df_PPT_set)
vctr_memory_ln <- NULL

for (i in 1:length(vctr_name_PPT)) {
  vctr_memory_ln[i] <-
    df_PPT_set %>% 
    pull(vctr_name_PPT[i]) %>% 
    model_W_linear(L_max = L_max_obs, theta_max = theta_max,
                   theta_init = theta_init_all) %$% 
    calc_memory(W_calc, t_step_hr = 24)
}

rslt_memory_exp <-
  data.frame(loss = "ln",
             PPT = vctr_name_PPT,
             plant = NA,
             meteo = NA,
             memory = vctr_memory_ln)


## non-linear loss model
vctr_name_meteo <- names(df_Rs_set)
vctr_name_plant <- c("sh", "fx", "ns")

vctr_type_PPT_nl <- NULL
vctr_type_plant_nl <- NULL
vctr_type_meteo_nl <- NULL
vctr_memory_nl <- NULL

for (i_PPT in 1:length(vctr_name_PPT)) {
  for (i_plant in 1:length(vctr_name_plant)) {
    for (i_meteo in 1:length(vctr_name_meteo)) {
      type_PPT_now <- vctr_name_PPT[i_PPT]
      type_plant_now <- vctr_name_plant[i_plant]
      type_meteo_now <- vctr_name_meteo[i_meteo]
      
      PPT_now <- df_PPT_set %>% pull(type_PPT_now)
      Rs_now <- df_Rs_set %>% pull(type_meteo_now)
      VPD_now <- df_VPD_set %>% pull(type_meteo_now)
      modify_ratio_Tr_now <- ifelse(type_plant_now == "ns", TRUE, FALSE)
      
      vctr_memory_nl <-
        model_W(PPT_now, Rs_now, VPD_now, vctr_Tr = NULL,
                K_sat_opt =
                  df_para_opt[df_para_opt$model == type_plant_now, ]$K_sat,
                b_opt = df_para_opt[df_para_opt$model == type_plant_now, ]$b,
                g_ref = coef(nls_Tr)[1, 1], Rs_max = 24.24,
                a1 = coef(nls_Tr)[2, 1], m = coef(nls_Tr)[4, 1],
                theta_max = theta_max, a2 = coef(nls_Tr)[3, 1],
                vctr_ratio_Tr =
                  df_para_opt[df_para_opt$model == type_plant_now, ]$ratio_Tr,
                theta_init = theta_init_all,
                modify_ratio_Tr = modify_ratio_Tr_now) %$% 
        calc_memory(W_calc, t_step_hr = 24) %>% 
        c(vctr_memory_nl, .)
      
      vctr_type_PPT_nl <- c(vctr_type_PPT_nl, type_PPT_now)
      vctr_type_plant_nl <- c(vctr_type_plant_nl, type_plant_now)
      vctr_type_meteo_nl <- c(vctr_type_meteo_nl, type_meteo_now)
    }
  }
}

## merge the results
rslt_memory_exp <-
  data.frame(loss = "nl",
             PPT = vctr_type_PPT_nl,
             plant = vctr_type_plant_nl,
             meteo = vctr_type_meteo_nl,
             memory = vctr_memory_nl) %>% 
  bind_rows(rslt_memory_exp, .)


# draw memory comparison graphs -------------------------------------------

size_axis_title <- 14
size_axis_text <- 12
size_anno_fignum <- 4
size_legend_title <- 4
size_legend_text <- 3.5

p_memory_model <-
  rslt_memory_exp %>% 
  filter((loss == "ln" & PPT == "av") |
           (loss == "nl" & PPT == "ob" & meteo == "ob")) %>% 
  bind_rows(., data.frame(loss = c(NA, NA),
                          PPT = c(NA, NA),
                          plant = c(NA, NA),
                          meteo = c(NA, NA),
                          memory = c(memory_obs, memory_DM88))) %>% 
  mutate(model = factor(c("Linear", "Case 1", "Case 2", "Case 3",
                          "Observed", "Evaporative"),
                        levels = c("Observed", "Evaporative", "Linear",
                                   "Case 1", "Case 2", "Case 3"))) %>% 
  ggplot()+
  theme_classic()+
  theme(axis.title = element_text(size = size_axis_title),
        axis.text.x = element_text(size = size_axis_text, colour = "black",
                                   hjust = 1, vjust = 1.0, angle = 30),
        axis.text.y = element_text(size = size_axis_text, colour = "black"),
        axis.ticks = element_line(colour = "black"),
        axis.ticks.length.x = unit(0, "mm"),
        axis.ticks.length.y = unit(3, "mm"),
        legend.position =  "none")+
  labs(x = "",
       y = bquote( Gamma[italic(w)]~(day) ))+
  scale_x_discrete(labels = c("Observed",
                              bquote(italic("\u03B7")*italic(Z)[r]/
                                       italic(L)[max]),
                              "Linear", "Case 1", "Case 2", "Case 3"))+
  scale_y_continuous(limits = c(0, 45), breaks = seq(0, 40, by = 10),
                     labels = c(0, "", 20, "", 40), expand = expansion())+
  scale_fill_manual(values = c("indianred2", "deepskyblue2", "gray80",
                               "gray50", "gray30", "gray10"), name = "")+
  geom_col(aes(model, memory/24, fill = model))+
  annotate("text", x = 1, y = Inf, label = "(e)", col = "black",
           size = size_anno_fignum, hjust = 1.2, vjust = 1)


p_memory_meteo <-
  rslt_memory_exp %>% 
  filter(loss == "nl" & plant == "ns" & PPT != "es") %>% 
  mutate(PPT = factor(PPT,
                      levels = c("av", "wt", "dr", "ss", "ob")),
         plant = factor(plant, levels = vctr_name_plant),
         meteo = factor(meteo, levels = c("ob", "eo", "so")))%>% 
  ggplot()+
  theme_classic()+
  theme(axis.title = element_text(size = size_axis_title),
        axis.text.x = element_text(size = size_axis_text, colour = "black",
                                   hjust = 1, vjust = 1.0, angle = 30),
        axis.text.y = element_text(size = size_axis_text, colour = "black"),
        axis.ticks = element_line(colour = "black"),
        axis.ticks.length.x = unit(0, "mm"),
        axis.ticks.length.y = unit(3, "mm"),
        legend.position = "none")+
  labs(x = "Precipitation type",
       y = "")+
  scale_x_discrete(labels = c("Averaged", "Wettest", "Driest",
                              "Monsoon-added", "Observed"))+
  scale_y_continuous(limits = c(0, 23), breaks = seq(0, 20, by = 5),
                     labels = c(0, "", 10, "", 20), expand = expansion())+
  scale_fill_manual(values = c("indianred2", "indianred2", "indianred2"),
                    name = "")+
  scale_alpha_manual(values = c(1, 0.6, 0.2))+
  geom_col(aes(PPT, memory/24, fill = meteo, alpha = meteo),
           position = "dodge")+
  annotate("text", x = 1, y = Inf, label = "(f)", col = "black",
           size = size_anno_fignum, hjust = 1.8, vjust = 1)+
  annotate("text", x = 0.52, y = 20, label = "Meteorology type",
           col = "black", size = size_legend_title, hjust = 0, vjust = 0.2)+
  annotate("rect", xmin = 0.52, xmax = 0.73, ymin = 18, ymax = 19,
           fill = "indianred2", alpha = 1)+
  annotate("rect", xmin = 0.52, xmax = 0.73, ymin = 16.5, ymax = 17.5,
           fill = "indianred2", alpha = 0.6)+
  annotate("rect", xmin = 0.52, xmax = 0.73, ymin = 15, ymax = 16,
           fill = "indianred2", alpha = 0.2)+
  annotate("text", x = 0.8, y = 18.5, label = "Observed", col = "black",
           size = size_legend_text, hjust = 0, vjust = 0.4)+
  annotate("text", x = 0.8, y = 17, label = "ENSO-omitted", col = "black",
           size = size_legend_text, hjust = 0, vjust = 0.4)+
  annotate("text", x = 0.8, y = 15.5, label = "Quasi-stationary",
           col = "black", size = size_legend_text, hjust = 0, vjust = 0.4)

p_memory <- p_memory_model | p_memory_meteo

# p_memory


## merge two figures
p_balance_ts_1by1_memory <-
  p_W_ts_calib /
  (p_1by1_balance_obsTr_sh | p_1by1_balance_obsTr_fx |
     p_1by1_balance_obsTr_ns) / p_memory +
  plot_layout(heights = c(1.2, 0.8, 1.5))

p_balance_ts_1by1_memory

# ggsave(file = "./LHP_SWC_validation_memory_ver01.pdf",
#        plot = p_balance_ts_1by1_memory, width = 190, height = 220,
#        units = "mm", device = cairo_pdf)


