
# lhp-soil-memory

<!-- badges: start -->
<!-- badges: end -->

This repository serves as an archive for the source code and datasets used in
the analysis for the article "Competing Controls of Hydroclimatic Variability
and Deep-Root Water Access on Soil Moisture Memory in a Bornean Rainforest."

## Contents

* src
  * LHP_soil_memory.R: Source code for all the analysis.
  
* data
  * LHP_30min.csv: Half-hourly time series observed at Lambir Hills National
  Park from November 1st 2009 to December 31st 2019, containing meteorological
  factors, eddy-covariance evapotranspiration, stand transpiration, and soil
  water content. The meteorological and eddy-covariance flux data were
  published in the
  [AsiaFlux Database](https://db.cger.nies.go.jp/asiafluxdb/?page_id=16).
  
  * LHP_daily.csv: Daily time series observed at Lambir Hills National Park
  from November 1st 2009 to December 31st 2019, containing meteorological
  factors and eddy-covariance evapotranspiration with a quality-control flag.
  
  * MEI_v2_JRA3Q.csv: Bi-monthly Multivariate El Niño/Southern Oscillation
  (ENSO) index (MEI.v2) from November 2009 to January 2020. The values were
  downloaded from the
  [NOAA Physical Sciences Laboratory](https://psl.noaa.gov/enso/mei/) and
  accessed on June 27th 2026.
