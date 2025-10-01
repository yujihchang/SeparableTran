#' An Unsupervised Adaptive Approach for Causal Inference in Competing Risks Data Using Separable Effects
#'
#' This package implements the methods proposed in the paper "An Unsupervised Adaptive Approach for Causal Inference in Competing Risks Data Using Separable Effects". It provides a semiparametric maximum likelihood estimator (SPMLE) under a full-likelihood and separable effects framework, and includes an unsupervised, AIC-based model selection procedure for semiparametric transformation models—specifically, generalized logarithmic and Box-Cox transformations—under competing risks settings.
#'
#' @param tt A numeric vector of time points at which the user is interested in calculating the effects, e.g., \code{c(12, 24, 36)}.
#' @param B1 Initial value for beta1. Numeric vector. Default is estimated from \code{coxph()}.
#' @param B2 Initial value for beta2. Numeric vector. Default is estimated from \code{coxph()}.
#' @param r1 Transformation tuning parameter for event time T1. Numeric. Default is chosen by model selection.
#' @param r2 Transformation tuning parameter for event time T2. Numeric. Default is chosen by model selection.
#' @param rr A numeric vector specifying the candidate range for the transformation tuning parameters \code{r1} and \code{r2}; e.g., \code{seq(0, 2, by = 0.01)}.
#' @param knots A numeric vector specifying the internal knots for cubic splines; e.g., \code{seq(0, 2, by = 0.5)}.
#' @param M A character string indicating transformation class: \code{"LT"} for logarithmic transformation, \code{"BCT"} for Box-Cox transformation. Default is \code{"LT"}.
#' @param con A character string to specify confounder adjustment method: \code{"user"}, \code{"median"}, or \code{"mean"}. Default is \code{"median"}.
#' @param level A numeric vector specifying specific levels for confounder adjustment. Default is \code{NULL}.
#' @param data A data frame containing the following columns:
#' \itemize{
#'   \item \code{X}: Observation time
#'   \item \code{D}: Censoring indicator (1 = event, 0 = censored)
#'   \item \code{K}: Competing risk indicator (1 = T1 event, 0 = T2 event)
#'   \item \code{Z}: Exposure and confounders (exposure should be the first column)
#' }
#'
#' @return An object of class "SepE" containing the following components:
#' \itemize{
#'   \item \code{r1}: Selected transformation tuning parameter for T1.
#'   \item \code{r2}: Selected transformation tuning parameter for T2.
#'   \item \code{coef.B1}: Estimated regression coefficients for T1 under specified transformation model.
#'   \item \code{coef.B2}: Estimated regression coefficients for T2 under specified transformation model.
#'   \item \code{base.R1}: Estimated baseline function for T1 under specified transformation model.
#'   \item \code{base.R2}: Estimated baseline function for T2 under specified transformation model.
#'   \item \code{DE}: Estimated separable direct effects.
#'   \item \code{IE}: Estimated separable indirect effects.
#'   \item \code{DE.sd}: Standard deviation of \code{DE}.
#'   \item \code{IE.sd}: Standard deviation of \code{IE}.
#'   \item \code{LG1}: Log-likelihood curve for T1 across the specified range of transformation tuning parameter.
#'   \item \code{LG2}: Log-likelihood curve for T2 across the specified range of transformation tuning parameter.
#' }
#' @import survival
#' @import splines
#' @export


SepE <- function(data, tt, B1 = NA, B2 = NA, r1 = NA, r2 = NA, rr = NA, knots = NA, M = "LT", con = "median", level = NULL, type = "right"){


  pLA <- function(yy, tt, LL){
    pla <- function(yi){
      loc <- sum(yi>=tt)
      if(loc==0)ans <- 0
      if(loc>0)ans <- LL[loc]
      ans
    }
    apply(matrix(yy),1,pla)
  }

  pLA_M <- function(yy, tt, LL){
    if(NCOL(LL)==1)LL <- matrix(LL)
    pla <- function(yi){
      loc <- sum(yi>=tt)
      if(loc==0)ans <- 0*LL[1,]
      if(loc>0)ans <- LL[loc,]
      as.numeric(ans)
    }
    apply(matrix(yy), 1, pla)
  }



  #Check the transformation model(log or Box-Cox)
  METH <- function(method = "LT"){
    if (method == "LT"){
      G  <- function(r, X){
        if(r == 0){
          L <- X}else{
          L <- log(1+r*X)/r}
      }

      dG <- function(d, r, X) {
        if (d == 0) {
          return(1 / (1 + r * X))
        } else if (d == 1) {
          return(-r / (1 + r * X)^2)
        } else if (d == 2) {
          return(2 * r^2 / (1 + r * X)^3)
        }
      }


    }else if (method == "BCT"){
      G  <- function(r, X){
        if(r == 0){
          L <- log(1+X)}else{
          L <- (((1+X)^r)-1)/r}
      }

      dG <- function(d, r, X) {
        if (d == 0) {
          return((1+X)^(r-1))
        } else if (d == 1) {
          return((r-1)*((1+X)^(r-2)))
        } else if (d == 2) {
          return((r-1)*(r-2)*((1+X)^(r-3)))
        }
      }

  }

  return(list(G = G, dG = dG))
  }

  meth <- METH(M)
  G  <- meth$G
  dG <- meth$dG


  #data sort
  DAT <- function(data, type){
    data <- data
    X  <- data$X
    D  <- data$D
    K  <- data$K
    if (type == "left"){
      A  <- data$A
      Z  <- data[,5:ncol(data)]
    }else if(type == "right"){
      A  <- X*0
      Z  <- data[,4:ncol(data)]
    }

    Z  <- as.matrix(Z)
    n  <- length(X)

    #讓event time 沒有重複
    Xt <- X+runif(n, min = 0, max = 0.0001)

    #排序
    Si <- sort(Xt, index.return=TRUE)
    Xs <- Xt[Si$ix]
    As <- A[Si$ix]
    Ds <- D[Si$ix]
    Ks <- K[Si$ix]
    Zs <- matrix(0, n, ncol(Z))
    for(i in 1:ncol(Z)){
      Zs[,i] <- Z[,i][Si$ix]
    }

    D1s <- Ds
    d1 <- which(Ks == 0) #T2 < T1
    D1s[d1] <- 0 #把被T2競爭蓋掉的變成0

    #一行一行填
    XXi <- matrix(Xs,n,n)
    #一列一列填
    XXj <- matrix(Xs,n,n,byrow=TRUE)
    #at risk matrix
    Y  <- ifelse(XXi >= XXj, 1, 0)
    #Xs[i] >= As (== TRUE)
    AA <- t(outer(Xs, As, ">="))
    Y  <- Y*AA
    D2s <- Ds
    d2 <- which(Ks == 1)#T1 <= T2
    D2s[d2] <- 0 #把被T1競爭蓋掉的變成0

    return(list(Xs = Xs, D1s = D1s, D2s = D2s, Zs = Zs, As = As, Y = Y))
  }

  #Estimation

  #Beta
  EST <- function(dat, B1, B2, r1, r2, M, BV = "TRUE", selec = "both"){

    meth <- METH(M)
    G  <- meth$G
    dG <- meth$dG

    IB <- function(r, X, D, Z, Zo2){
      g   <- dG(0, r, X)
      gd  <- dG(1, r, X)
      gdd <- dG(2, r, X)
      Part1 <- g-D*gd/g
      Part2 <- gd-D*(gdd*g-gd^2)/g^2

      db  <- apply(-Part1*X*Z + D*Z, 2, sum)
      dbb <- apply(Part2*X^2*Zo2 + Part1*X*Zo2, 2, sum)

      return(list(dBB = dbb, dB = db))
    }


    dat <- dat
    Xs  <- dat$Xs
    D1s <- dat$D1s
    D2s <- dat$D2s
    Zs  <- dat$Zs
    Y   <- dat$Y

    a <- 0
    B1 <- B1
    B2 <- B2
    Rhat1 <- Xs
    Rhat2 <- Xs
    score1 <- c(10,10)
    score2 <- c(10,10)
    while(max(abs(score1))> 0.00001 & max(abs(score2)) > 0.00001){
      RR  <- RHAT(dat, B1, B2, r1, r2, Rhat1, Rhat2, M)
      Rhat1 <- RR$Rhat1
      Rhat2 <- RR$Rhat2

      N   <- length(Xs)
      B1m <- matrix(B1, N, length(B1), byrow = TRUE)
      bz1  <- apply(B1m*Zs, 1, sum)
      exb1 <- exp(bz1)
      B2m <- matrix(B2, N, length(B2), byrow = TRUE)
      bz2  <- apply(B2m*Zs, 1, sum)
      exb2 <- exp(bz2)

      Zo2 <- c()
      #Z1,Z1Z2,Z2Z1,Z2
      for(i in 1:N){Zo2=rbind(Zo2,c(t(Zs[i,])%x%Zs[i,]))}
        XX1  <- Rhat1*exb1
        Isc1  <- IB(r1, XX1, D1s, Zs, Zo2)
        Iij1 <- Isc1$dBB
        I1 <- matrix(Iij1, length(B1), length(B1))
        score1 <- Isc1$dB
        B1f <- B1
        B1  <- B1+score1%*%solve(I1)
        B1d <- B1-B1f

        #B2開始

        XX2 <- Rhat2*exb2
        Isc2 <- IB(r2, XX2, D2s, Zs, Zo2)
        Iij2 <- Isc2$dBB
        I2 <- matrix(Iij2, length(B2), length(B2))
        score2 <- Isc2$dB
        B2f <- B2
        B2  <- B2+score2%*%solve(I2)
        B2d <- B2-B2f
        a <- a+1
        cat("Iteration:", a, "\n")
        cat("Bhat1:", B1, "\n")
        cat("Bhat2:", B2, "\n")
        if (selec == "both"){
          bb1 <- max(abs(B1d))
          bb2 <- max(abs(B2d))
        }else if (selec == "bt1"){
          bb1 <- max(abs(B1d))
          bb2 <- 0
        }else if (selec == "bt2"){
          bb1 <- 0
          bb2 <- max(abs(B2d))
        }else{
          bb1 <- "If you are performing model selection, choose one variable you care about."
          bb2 <- "If you are performing model selection, choose one variable you care about."
          print(bb1)
        }


    if (bb1 < 0.00001 & bb2 < 0.00001){break}
    }

    R1  <- RR$Rhat1
    dR1 <- diff(c(0,R1))
    R2  <- RR$Rhat2
    dR2 <- diff(c(0,R2))
    B1h <- B1
    B2h <- B2

    if (BV == "FALSE"){
      dbb1 <- NULL
      dbr1 <- NULL
      drr1 <- NULL
      dbb2 <- NULL
      dbr2 <- NULL
      drr2 <- NULL
    }

    if (BV == "TRUE"){
      clean1  <- CL(Zs, B1h, R1)
      clean2  <- CL(Zs, B2h, R2)
      XX1  <- clean1$XX
      exb1 <- clean1$exb
      XX2  <- clean2$XX
      exb2 <- clean2$exb

      varB1 <- GBF(r1, XX1, Y, D1s, Zs, Zo2, exb1, dR1)
      varB2 <- GBF(r2, XX2, Y, D2s, Zs, Zo2, exb2, dR2)

      dbb1 <- varB1$dBB
      dbr1 <- varB1$dBR
      drr1 <- varB1$dRR

      dbb2 <- varB2$dBB
      dbr2 <- varB2$dBR
      drr2 <- varB2$dRR
    }

  return(list(Y = Y, Xs = Xs, Zs = Zs, Bhat1 = B1, Bhat2 = B2, Rhat1 = R1, Rhat2 = R2, rhat2 = dR2, D1s = D1s, D2s = D2s, DBB1 = dbb1, DBB2 = dbb2, DBR1 = dbr1, DBR2 = dbr2, DRR1 = drr1, DRR2 = drr2))
  }


  CL <- function (Z, B, R){
    N   <- length(Xs)
    Bm <- matrix(B, N, length(B), byrow = TRUE)
    bz  <- apply(Bm*Z, 1, sum)
    exb <- exp(bz)
    XX <- R*exb
    return(list(XX = XX, exb = exb))
  }


  GBF <- function(r, X, Y, D, Z, Zo2, exb, dR){
    ax   <- which(D == 1)
    ddR  <- c()

    dbb <- matrix(0, ncol(Z), ncol(Z))
    dbr <- matrix(0, length(ax), ncol(Z))
    drr <- matrix(0, length(ax), length(ax))

    g   <- dG(0, r, X)
    gd  <- dG(1, r, X)
    gdd <- dG(2, r, X)

    Part1 <- g-D*gd/g
    Part2 <- gd-D*(gdd*g-gd^2)/g^2

    dbb <- apply(Part2*X^2*Zo2 + Part1*X*Zo2, 2, sum)

    YY_1  <- Part1 *Y*exb
    YY_2  <- Part2 *Y*exb*X
    YY_3  <- Part2 *Y*exb^2

    for (i in 1:length(ax)){
      dbr[i,] <- apply(YY_1[,ax[i]]*Z + YY_2[,ax[i]]*Z, 2, sum)
    }


    ddR <- D[ax]/dR[ax]^2

    for (i in 1:length(ax)){
      drr[i,i] <- sum(YY_3[,ax[i]])+ddR[i]
    }

    #旁邊dR_j+dR_p
    for (i in 1:(length(ax)-1)){
      for (p in (i+1):length(ax)){
        drr[i,p] <- sum(YY_3[,ax[p]])
        drr[p,i] <- sum(YY_3[,ax[p]])
      }
    }

    return(list(dBB = dbb, dBR = dbr, dRR = drr))
  }

  #R
  RHAT <- function(dat, B1, B2, r1, r2, Rhat1, Rhat2, M){

    meth <- METH(M)
    G  <- meth$G
    dG <- meth$dG

    dat <- dat
    D1s <- dat$D1s
    D2s <- dat$D2s
    Zs  <- dat$Zs
    Y   <- dat$Y

    haz <- function (Z, B, r, R, D, Y){
      N   <- nrow(Zs)
      Bm <- matrix(B, n, length(B), byrow = TRUE)
      bz  <- apply(Bm*Z, 1, sum)
      exb <- exp(bz)
      XX <- R*exb
      g   <- dG(0, r, XX)
      gd  <- dG(1, r, XX)
      s0    <- g*exb - D*(gd/g)*exb
      S0    <- apply(Y*s0, 2, sum)
      dR <- D/S0
    }

    for(h in 1:10){
      dR1 <- haz(Zs, B1, r1, Rhat1, D1s, Y)

      Rhat1 <- cumsum(dR1) #cumutative hazard
    }

    for(p in 1:10){
      dR2 <- haz(Zs, B2, r2, Rhat2, D2s, Y)

      Rhat2 <- cumsum(dR2) #cumutative hazard
    }


    return(list(D1s = D1s, D2s = D2s, Rhat1 = Rhat1, Rhat2 = Rhat2, rhat2 = dR2))
  }

  #排矩陣
  IMt <- function(B1, D1s, D2s, dbb1, dbb2, dbr1, dbr2, drr1, drr2){

    P <- length(B1)
    S <- sum(D1s)+sum(D2s)
    #左上
    IM_dbb <- matrix(0, 2*P, 2*P)
    IM_dbb[1:P, 1:P] <- dbb1
    IM_dbb[(P+1):(P+P), (P+1):(P+P)] <-   dbb2

    #右上
    IM_dbr <- matrix(0, 2*P, S)
    IM_dbr[1:P, 1:sum(D1s)] <- t(dbr1)
    IM_dbr[(P+1):(P+P), (sum(D1s)+1):S] <- t(dbr2)

     #左下
     IM_drb <- matrix(0, S, 2*P)
     IM_drb <- t(IM_dbr)

     #右下
    IM_drr <- matrix(0, S, S)
    IM_drr[1:sum(D1s), 1:sum(D1s)] <- drr1
    IM_drr[(sum(D1s)+1):S, (sum(D1s)+1):S] <- drr2


    IM <- rbind(cbind(IM_dbb, IM_dbr), cbind(IM_drb, IM_drr))

    return(IM)
  }


  LLL <- function(est, y1, y2, tt, r1, r2, con, level, M){
    meth <- METH(M)
    G  <- meth$G
    dG <- meth$dG
    Xs  <- est$Xs
    D1s <- est$D1s
    D2s <- est$D2s
    Zs  <- est$Zs
    Y   <- est$Y
    R1h <- est$Rhat1
    R2h <- est$Rhat2
    B1h <- est$Bhat1
    B2h <- est$Bhat2
    a <- which(D1s == 1)
    b <- which(D2s == 1)


    #FOR F
    Z1s <- Zs[,1]

    if (ncol(Zs) == 1){

      Z2s = Z2M = 0
    }else{

      Z2s <- Zs[,2:ncol(Zs)]

      if (con == "median"){
        Z2M <- apply(as.matrix(Z2s), 2, median)
      }else if (con == "mean"){
        Z2M <- apply(as.matrix(Z2s), 2, mean)
      }else if (con == "user"){
        Z2M <- level
      }else{
        Z2M <- "Invalid con value. Please choose 'median' or 'mean'."
        print(Z2M)
      }

    }


    Bo1   <- B1h[-1]
    eb1w  <- exp( sum(Bo1*Z2M) )
    eb1z  <- exp(B1h[1]*y1)

    Bo2   <- B2h[-1]
    eb2w  <- exp( sum(Bo2*Z2M) )
    eb2z  <- exp(B2h[1]*y2)

    XX1   <- R1h*eb1z*eb1w
    G1    <- G(r1, XX1)
    g1    <- dG(0, r1, XX1)

    XX2    <- R2h*eb2z*eb2w
    G2     <- G(r2, XX2)
    g2     <- dG(0, r2, XX2)

    XX1s <- pLA(Xs, Xs, XX1)
    G1s  <- pLA(Xs, Xs, G1)
    g1s  <- pLA(Xs, Xs, g1)
    XX2s <- pLA(Xs, Xs, XX2)
    G2s  <- pLA(Xs, Xs, G2)
    g2s  <- pLA(Xs, Xs, g2)

    g2_exb <- g2s*eb2z*eb2w*Y
    g2_XX2 <- g2s*XX2s

    dg2_XX2 <- diff(c(0, g2_XX2))
    dG2     <- diff(c(0, G2s))



    FG     <- dG2    *exp( -G2s - G1s )
    Fg_XX2 <- dg2_XX2*exp( -G2s - G1s )

    F  <- cumsum(FG)
    Ft <- pLA(tt, Xs, F)

  ########################
  #                      #
  #    Delta Method      #
  #                      #
  ########################


  ##########################
  #                        #
  # Delta Method for Beta  #
  #	                   #
  ##########################

    if (ncol(Zs) == 1){
      Z2M = NULL
  }


    #B1微
    dfb1 <- - matrix(c(y1,Z2M), length(Xs), ncol(Zs),byrow=TRUE)*cumsum( XX1s*g1s*FG )


    #B2微
    dfb2 <-
    matrix(c(y2,Z2M), length(Xs), ncol(Zs),byrow=TRUE)*cumsum(                  Fg_XX2    )-
    matrix(c(y2,Z2M), length(Xs), ncol(Zs),byrow=TRUE)*cumsum(                  FG*g2s*XX2s )


    DB <- cbind(dfb1, dfb2)

  ###########################
  #                         #
  # Delta Method for Lambda #
  #	                    #
  ###########################
    a <- which(D1s == 1)
    b <- which(D2s == 1)

    # T1_jump


    dFR1  <- -FG*g1s*eb1z*eb1w
    dfr1  <- apply(dFR1[b]*Y[b,a], 2, cumsum)
    dfr1  <- pLA_M(tt ,Xs[D2s > 0], dfr1)



    # T2_jump

    dFR2 <- -FG*g2s*eb2z*eb2w
    Fg   <- apply(apply(g2_exb, 2, function(x) diff(c(0, x)))*exp( -G2s - G1s ), 2, cumsum)

    dfr2 <- apply(dFR2[b]*Y[b,b], 2, cumsum)+ Fg[b,b]
    dfr2 <- pLA_M(tt, Xs[D2s > 0], dfr2)

    DR <- rbind(dfr1, dfr2)

    DBt <- pLA_M(tt, Xs, DB)

    DD  <- rbind(DBt, DR)



    return(list(Ft = Ft, DD = DD))

  }






  #Model selection

  FF <- function(Ds, dR, bz, r, Rhat){
    exb <- exp(bz)
    if(Ds == 1){
      f2 <- Ds*(log(dR)+log(dG(0, r, Rhat*exb)) + bz)
    }else{
      f2 <- 0
    }
    return(f2)
  }

  LOG <- function(B, Z, r, Rhat, dR, Ds){
    ll  <- c()
    N   <- length(Rhat)
    Bm  <- matrix(B, N, length(B), byrow = TRUE)
    bz  <- apply(Bm*Z, 1, sum)
    exb <- exp(bz)
    XX  <- Rhat*exb
    for (k in 1:length(XX)){
        ll[k] <- -G(r, XX[k]) + FF(Ds[k], dR[k], bz[k], r, Rhat[k])
    }
    lbr <- sum(ll)
    lbr
  }

  dat <- DAT(data, type)
  Xs  <- dat$Xs
  D1s <- dat$D1s
  D2s <- dat$D2s
  Zs  <- dat$Zs
  n   <- length(Xs)

  if (all(is.na(B1)) && all(is.na(B2))){
    B1 <- coxph(Surv(Xs, D1s)~Zs)$coef
    B2 <- coxph(Surv(Xs, D2s)~Zs)$coef
  }else{
    B1 <- B1
    B2 <- B2
  }

  #selection(Yes/No)
  if(is.na(r1)){
    if(any(is.na(rr)) | any(is.na(knots))){
      print("You need to decide the 'r1' range and the number of knots when doing model selection.")}
    }

  if(is.na(r2)){
    if(any(is.na(rr)) | any(is.na(knots))){
      print("You need to decide the 'r2' range and the number of knots when doing model selection.")}
    }

  rr <- rr
  #smoothing knots
  knots <- knots
  lg1s <- c()
  if (is.na(r1)){
    for (w in 1:length(knots)){
      B1 <- B1
      B2 <- B2
      est  <- EST(dat, B1, B2, knots[w], 1, M, BV = "FALSE")
      R1   <- est$Rhat1
      dR1 <- diff(c(0,R1))
      B1h <- est$Bhat1
      D1s <- est$D1s
      Zs  <- est$Zs
      lg1s[w] <- LOG(B1h, Zs, knots[w], R1, dR1, D1s)
    }


    fit    <- lm(lg1s ~ ns(knots, df = (length(knots)-1) ))
    y_pred <- predict(fit, newdata = data.frame(knots = rr))

    Si <- sort(y_pred, index.return = TRUE, decreasing = TRUE)
    r1_s <- rr[Si$ix]
    r1s <- r1_s[1]

    LG1s <- y_pred
    r1m  <- r1s
  }else{
    LG1s <- NULL
    r1m  <- r1
  }


  lg2s <- c()
  if (is.na(r2)){
    for (w in 1:length(knots)){
      B1 <- B1
      B2 <- B2
      est  <- EST(dat, B1, B2, 1, knots[w], M, BV = "FALSE")
      R2  <- est$Rhat2
      dR2 <- diff(c(0,R2))
      B2h <- est$Bhat2
      D2s <- est$D2s
      Zs  <- est$Zs
      lg2s[w] <- LOG(B2h, Zs, knots[w], R2, dR2, D2s)
    }

    fit2    <- lm(lg2s ~ ns(knots, df = (length(knots)-1) ))
    y_pred2 <- predict(fit2, newdata = data.frame(knots = rr))

    Si <- sort(y_pred2, index.return = TRUE, decreasing = TRUE)
    r2_s <- rr[Si$ix]
    r2s <- r2_s[1]

    LG2s <- y_pred2
    r2m  <- r2s
  }else{
    LG2s <- NULL
    r2m  <- r2
  }

  #Effects


  #Initial Value (CoxPH)

  B1 <- B1
  B2 <- B2
  est  <- EST(dat, B1, B2, r1m, r2m, M)
  B1h  <- est$Bhat1
  B2h  <- est$Bhat2
  R1h  <- est$Rhat1
  R2h  <- est$Rhat2
  dbb1 <- est$DBB1
  dbb2 <- est$DBB2
  dbr1 <- est$DBR1
  dbr2 <- est$DBR2
  drr1 <- est$DRR1
  drr2 <- est$DRR2
  A01  <- LLL(est, 0, 1, tt, r1m, r2m, con, level, M)
  A00  <- LLL(est, 0, 0, tt, r1m, r2m, con, level, M)
  A11  <- LLL(est, 1, 1, tt, r1m, r2m, con, level, M)

  DE <- A01$Ft - A00$Ft
  IE <- A11$Ft - A01$Ft

  IM  <- IMt(B1, D1s, D2s, dbb1, dbb2, dbr1, dbr2, drr1, drr2)
  C   <- solve(IM)

  DD01 <- A01$DD
  DD00 <- A00$DD
  DD11 <- A11$DD

  DE.var <- c()
  IE.var <- c()

  for(pptt in 1:length(tt)){

    dDE <- DD01[,pptt]-DD00[,pptt]
    dIE <- DD11[,pptt]-DD01[,pptt]


    DE.var[pptt] <- t(dDE)%*%C%*%dDE
    IE.var[pptt] <- t(dIE)%*%C%*%dIE

  }


  report=list(
    r1 = r1m,
    r2 = r2m,
    coef.B1 = B1h,
    coef.B2 = B2h,
    base.R1 = R1h,
    base.R2 = R2h,
    DE = DE,
    IE = IE,
    DE.sd = sqrt(DE.var),
    IE.sd = sqrt(IE.var),
    LG1 = LG1s,
    LG2 = LG2s
  )
  return(report)

}

