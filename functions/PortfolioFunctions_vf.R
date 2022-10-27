################################################################################
##################        Portfolio Functions
################################################################################

library('Sim.DiffProc')
library('dplyr')
library('tidyr')
library('quadprog')
library('ggplot2')
library('ggforce')
library('mbend')
library('abind')
library('matrixcalc')


options(scipen = 999)
#*******************************************************************************
#  I .- Function to get returns
getReturns<-function(x, simple=FALSE){
  names<-c(names(x)[-1])
  time<-x[-1,1]
  x<-as.matrix(x[,-1],ncol=ncol(x[,-1]),byrow=FALSE) 
  B<- matrix(ncol=ncol(x),nrow=nrow(x)-1)
  for(i in 1:ncol(x)){
    if(simple){
      B[,i] <- (exp(diff(log(x[,i]),lag=1)) - 1)
    }else{
      B[,i]<-diff(log(x[,i]),lag=1)
    }
        
  }
  B<-data.frame(B)     
  colnames(B)<-names
  C<-data.frame(Fecha=time,B)
  return(C)
}


#**************************************************************************
# II.- Portfolio optimization
getMinPortfolio<-function(r.e, mat.cov){
  Dmat <- 2*mat.cov   
  dvec <- rep.int(0, length(r.e))     
  Amat <- cbind(rep(1,length(r.e)),  # res1:  sum w_i = 1
                diag(1,length(r.e)), # res2:  w_i > 0              
                -diag(1,length(r.e))) # res3: w_i <= b  => - w_i >= b
  bvec <- c(1,                  # res1                                 
            rep(0,length(r.e)), # res2
            -rep(1,length(r.e))) # res3
  
  result <- solve.QP(Dmat=Dmat,dvec=dvec,Amat=Amat,bvec=bvec,meq=1)
  w.min <- round(result$solution, 4)
  
  names(w.min) <- names(r.e)
  port.min <- list("pesos" = w.min)
  return(port.min) 
}

#*************************************************************************
# III. Portfolio returns
getPortfolioReturns <-function(returns, weights){
  #w<- rep(weights,nrow(returns))
  r.port <- NULL
  for(i in 1:nrow(returns)){
    r.port[i] <- sum(weights*returns[i,-1]) 
  }
  return(r.port)
}
# portfolio expected return
getPortfolio.re <-function(r.e, weights){
  re.p.min <- crossprod(weights, r.e)
  return(re.p.min)
}
# portfolio sd
getPortfolio.sd <-function(mat.cov, weights){
  sd.p.min <- sqrt(t(weights) %*% mat.cov %*% weights)
  return(sd.p.min)
}

#*******************************************************************************
#  IV.  Top_n stocks
top_n <- function(returns, sorted_by='mean', top=top.k){
  df_stat <- returns %>% 
    gather(key='asset',value='valor',-Fecha) %>%
    group_by(asset) %>%
    summarise(n = n(), 
              mean = mean(valor), 
              sd = sd(valor),
              sr = mean / sd, 
              min = min(valor),
              max = max(valor),
              skeness = skewness(valor),
              kurtosis = kurtosis(valor)) %>%
    ungroup()%>%data.frame()
  
  # condition
  if(sorted_by == 'mean'){
    df_stat <- df_stat %>% arrange(desc(mean))
  } else if(sorted_by == 'sd'){
    df_stat <- df_stat %>% arrange(desc(sd))
  } else {
    df_stat <- df_stat %>% arrange(desc(sr))
  }
  
  topn <- df_stat$asset[1:top]
  df  <- returns[,c('Fecha',topn)]
  return(df)
  
}

#*******************************************************************************
# V. Random weights
random_weights <- function(n_assets){
  weights <- c()
  for(i in 1:(n_assets-1)){
    if(i == 1){
      weights[i] <- sample(10000,1,replace = TRUE)
    } else{
      weights[i] <- sample((10000-sum(weights)),1,replace = TRUE)
    }
  }
  weights[n_assets] <- 10000 - sum(weights)
  return(sample(weights,n_assets,replace=FALSE)/10000)
} 

#*******************************************************************************
#  VII. Covariance at time t
cov.md <- function(base){
  # input:
  #   base : returns with date as first column
  # output:
  #   array 3-dimensional (1-2d covariance, 3d time)
  for(i in 2:nrow(base)){
    if(i == 2){
      arr <- cov(base[1:i,-1])
    } else{
      df <- cov(base[1:i,-1])
      arr <- abind(arr, df, along=3)
    }
  }
  dimnames(arr)[[3]] <- as.vector(as.character(base$Fecha[-1]))
  
  return(arr)
}

#*******************************************************************************
#  VIII. Difference mean returns at time t
diff.rett <- function(base){
  # input:
  #   base: returns' matrix with Date as first column 
  ############ mean returns at time t
  cnames <- colnames(base[,-1])
  rnames <- base[-1,1]
  for(i in 2:nrow(base)){
    if(i == 2){
      v.mean <- apply(base[1:i,-1], 2, mean)
    } else{
      df <- apply(base[1:i,-1], 2, mean)
      v.mean <- rbind(v.mean, df)
      rownames(v.mean) <- NULL
    }
  }
  df_means <- data.frame('Date'=rnames, v.mean)
  ############# multi-d matrix of difference mean(r_i) - mean(r_j)
  md.means <- NULL
  for(j in 1:nrow(df_means)){
    mat.m <-  matrix(0, nrow=length(cnames), ncol=length(cnames))
    for(i in 1:length(cnames)){
      pivot <- df_means[j, i+1]
      v.m <- df_means[j,]
      for(k in 1:length(cnames)){
        # diagonal distance
        if(i == k){ 
          mat.m[i, k] <- abs(pivot - v.m[1,k+1])
          # out of diagonal
        } else{
          mat.m[i, k] <- abs(pivot - v.m[1,k+1])
        }
      }
    }
    md.means <- abind(md.means, mat.m, along=3)
  }
  dimnames(md.means)[[1]] <- cnames
  dimnames(md.means)[[2]] <- cnames
  dimnames(md.means)[[3]] <- as.vector(as.character(rnames))
  
  return(md.means)
}

#*******************************************************************************
#  IX. Fitting model at time t
new.cov <- function(x){
  # sample covariance 3d
  #x <- ret
  cv_md <- cov.md(x)
  diff.ret <-  diff.rett(x)
  # symbols
  n <- dimnames(cv_md)[[1]]
  m <- dimnames(cv_md)[[2]]
  date <- x[-1,1]
  # matrix initialization
  mat <- array(0, dim=c(length(n), length(m), nrow(x)-1))
  # for loop initialization
  for(j in 1:length(n)){
    for(i in 1:length(m)){
      # expected returns
      re.n <- mean(x[, n[i]])
      re.m <- mean(x[, m[j]])
      # dataframe 
      df <- 
        data.frame('t'=2:nrow(x), 
                   'cov'= cv_md[i,j,],
                   'diff'=diff.ret[i,j,]) %>% 
        mutate('log'=log(abs(cov)))
     
      # condition to estimate beta
      if(i != j){
        # fit model
        model <- lm(log~t+diff, data=df)
        # parameters
        alpha <- as.numeric(model$coefficients[1])
        gamma <- as.numeric(model$coefficients[2])
        beta <- as.numeric(model$coefficients[3])        
      }else{
        # fit model
        model2 <- lm(log~t, data=df)
        # parameters
        alpha <- as.numeric(model2$coefficients[1])
        gamma <- as.numeric(model2$coefficients[2])
        beta <- 0    
      }
      for(k in 1:nrow(df)){
        mat[i,j,k] <- as.vector(exp(alpha)*exp(- beta*df$diff[k])*(1-exp(- gamma*df$t[k])))
      }
      colnames(mat) <- n
      rownames(mat) <- m
    }
  }
  dimnames(mat)[[3]] <- as.vector(as.character(date))
  
  return(mat)
}

#******************************************************************************
#* Function to estimate covariance matrix (predicted values)
new.cov2 <- function(x, n.ahead=10){
  # sample covariance 3d
  cv_md <- cov.md(x)
  diff.ret <-  diff.rett(x)
  # symbols
  n <- dimnames(cv_md)[[1]]
  m <- dimnames(cv_md)[[2]]
  # matrix initialization
  mat <- array(0, dim=c(length(n), length(m), nrow(x)-1))
  mat.pred <- matrix(0, ncol=length(n), nrow=length(m), dimnames = list(n,m))
  # for loop initialization
  for(j in 1:length(n)){
    for(i in 1:length(m)){
      # expected returns
      re.n <- mean(x[, n[i]])
      re.m <- mean(x[, m[j]])
      # dataframe 
      df <- 
        data.frame('t'=6:nrow(x), 
                   'y'= cv_md[i,j,-c(1:4)],
                   'x'=diff.ret[i,j, -c(1:4)]) %>% 
        mutate('log_y'=ifelse(y != 0,  log(abs(y)),  0))
      # condition to estimate parameters
      if(i != j){
        # fit model
        model2 <- lm(log_y~t+x, data=df)
        # parameters
        alpha <- as.numeric(model2$coefficients[1])
        gamma <- as.numeric(model2$coefficients[2])
        beta <- as.numeric(model2$coefficients[3])        
      }else{
        # fit model
        model2 <- lm(log_y~t, data=df)
        # parameters
        alpha <- as.numeric(model2$coefficients[1])
        gamma <- as.numeric(model2$coefficients[2])
        beta <- 0    
      }
      # newdata
      t.last <- df$t[nrow(df)]
      diff.last <- df$x[nrow(df)]
      newdata <- data.frame('t'=(t.last+n.ahead), 
                            'x'=(diff.last))
      # predicted matrix
      mat.pred[i,j] <- exp(alpha)*exp(- beta*diff.last)*(1-exp(- gamma*(t.last+n.ahead)))
      # nonlinear model
      # variances and covariances
      for(k in 1:nrow(df)){
        mat[i,j,k] <- exp(alpha)*exp(- beta*df$x[k])*(1-exp(- gamma*df$t[k]))
      }
      colnames(mat) <- n
      rownames(mat) <- m
    }
  }
  result <- mat.pred
  return(result)
}


# covariance and correlation
cov.cor <- function(returns){
  
  cov2 <- cov(returns)
  # correlation matrix
  cor2 <- cor(returns)
  # init. matrix
  cov.diag <-matrix(0, ncol=ncol(cov2), nrow=nrow(cov2))
  colnames(cov.diag) <- colnames(cov2)
  rownames(cov.diag) <- rownames(cov2)
  # for loop
  for(i in 1:ncol(cov2)){
    for(j in 1:nrow(cov2)){
      if(i == j){
        cov.diag[i, j] <- cov2[i, j] / max(as.vector(diag(cov2)))
      }else{
        cov.diag[i, j] <- cor2[i, j]
      }
    }
  }
  return(cov.diag)
}

# considering independence
var.diag <- function(returns){
  # covariance
  cov2 <- cov(returns)
  # correlation matrix
  #cor2 <- cor(returns)
  # init. matrix
  cov.diag <-matrix(0, ncol=ncol(cov2), nrow=nrow(cov2))
  colnames(cov.diag) <- colnames(cov2)
  rownames(cov.diag) <- rownames(cov2)
  # for loop
  for(i in 1:ncol(cov2)){
    for(j in 1:nrow(cov2)){
      if(i == j){
        cov.diag[i, j] <- cov2[i, j] 
      }else{
        cov.diag[i, j] <- 0
      }
    }
  }
  return(cov.diag)
}

#*******************************************************************************
#  VII. Variance and covariance matrix     

mat_cov <- function(base_roll, type='mv'){
  if (type == 'mv'){
    mat.cov <- cov(as.matrix(base_roll[,-1]))
  } else if(type =='cor'){
    if(!is.positive.definite(cov.cor((base_roll[,-1])))){
      mat.cov <- bend(cov.cor((base_roll[,-1])), small.positive=0.00001, method='hj')$bent
    }
    mat.cov <- cov.cor(as.matrix(base_roll[,-1]))
  } else if(type =='var'){
    mat.cov <- var.diag((base_roll[,-1]))
  } else if(type == 'gbm'){
    t <- base_roll%>%nrow()
    names <- colnames(base_roll[,-1])
    e.r <- NULL
    sd.r <- NULL
    for(i in 1:length(names)){
      X <- base_roll[,i+1]
      est <- param_estimation(X)
      e.r[i] <- est[1]
      sd.r[i] <- est[2]
    }
    # expected value and risk 
    r.e_roll <- ((e.r - sd.r^2)/2)*t
    mat.cov_roll <- cov(base_roll[,-1])
    mat.cov_roll2 <- matrix(0,ncol=ncol(mat.cov_roll),nrow=nrow(mat.cov_roll))
    
    for(i in 1:ncol(mat.cov_roll)){
      for(j in 1:nrow(mat.cov_roll)){
        if(i != j){
          mat.cov_roll2[j,i] <- sd.r[j]*sd.r[i]*cor(base_roll[,j+1],base_roll[,i+1])
        } else{
          mat.cov_roll2[j,i] <- sd.r[i]^2
        }
        
      }
    }
    mat.cov <- mat.cov_roll2*t
  } else{
    stocks_selected <- colnames(base_roll[,-1])
    last_date <- as.character(base_roll[nrow(base_roll), 1])
    #print(last_date)
    mat.cov <- round((cov.estimated[stocks_selected, stocks_selected, last_date]),7)
    #print(mat.cov)
    if(!is.positive.definite(mat.cov)){
      mat.cov <- bend(mat.cov, small.positive=0.00001, method='hj')$bent
    }
  }
  return(mat.cov)
}

#*******************************************************************************
#*  Second option 
#*  
mat_cov2 <- function(base_roll, type='mv', n.ahead=10){
  if (type == 'mv'){
    mat.cov <- cov(as.matrix(base_roll[,-1]))
  } else if(type =='cor'){
    if(!is.positive.definite(cov.cor((base_roll[,-1])))){
      mat.cov <- bend(cov.cor((base_roll[,-1])), small.positive=0.00001, method='hj')$bent
    }else{
      mat.cov <- cov.cor(as.matrix(base_roll[,-1]))
    }
  } else if(type == 'gbm'){
    t <- base_roll%>%nrow()
    names <- colnames(base_roll[,-1])
    e.r <- NULL
    sd.r <- NULL
    for(i in 1:length(names)){
      X <- base_roll[,i+1]
      est <- param_estimation(X)
      e.r[i] <- est[1]
      sd.r[i] <- est[2]
    }
    # expected value and risk 
    r.e_roll <- ((e.r - sd.r^2)/2)*t
    mat.cov_roll <- cov(base_roll[,-1])
    mat.cov_roll2 <- matrix(0,ncol=ncol(mat.cov_roll),nrow=nrow(mat.cov_roll))
    
    for(i in 1:ncol(mat.cov_roll)){
      for(j in 1:nrow(mat.cov_roll)){
        if(i != j){
          mat.cov_roll2[j,i] <- sd.r[j]*sd.r[i]*cor(base_roll[,j+1],base_roll[,i+1])
        } else{
          mat.cov_roll2[j,i] <- sd.r[i]^2
        }
        
      }
    }
    mat.cov <- mat.cov_roll2*t
  } else{
    # estimated covariance
    cov.estimated <- new.cov2(base_roll, n.ahead)
    stocks_selected <- colnames(base_roll[,-1])
    last_date <- as.character(base_roll[nrow(base_roll), 1])
    #print(last_date)
    #mat.cov <- round((cov.estimated[stocks_selected, stocks_selected, last_date]),7)
    mat.cov <- cov.estimated
    #print(mat.cov)
    if(!is.positive.definite(mat.cov)){
      mat.cov <- bend(mat.cov)$bent
    }
  }
  return(mat.cov)
}

#*******************************************************************************
# VII. Function to match weights

all_weights <- function(base,pesos){
  mat.weights <- data.frame(matrix(0,ncol=length(base[,-1]),nrow=1))
  colnames(mat.weights) <- colnames(base[,-1])
  mat.weights[,names(pesos)] <- pesos
  return(mat.weights)
}


#*******************************************************************************
# VIII. Portfolio weights
getPortfolio <- function(base, year_to_start, rebalance_period=24, mod='mv', sorted='mean', top.k=10){
  # returns
  df_rend <- getReturns(base)
  # filter assets
  assets <- colnames(df_rend[,-1]) 
  # returns
  df_rend2 <- df_rend%>%
    gather(key='asset',value='valor',-Fecha)%>%
    filter(asset %in% assets)%>%
    spread(asset,valor)%>%
    mutate(Fecha = as.Date(Fecha,"%d/%m/%Y"),
           year = format(Fecha, '%Y'),
           month = format(Fecha, '%m'),
           year_month_index=paste(year,month,sep='-'))
  # create sequence of periods
  initial.periods <- unique(df_rend2$year_month_index)[1:(length(unique(df_rend2$year_month_index))-which(unique(df_rend2$year_month_index)==paste(year_to_start,'01',sep='-'))+1)]
  final.periods <- unique(df_rend2$year_month_index)[which(unique(df_rend2$year_month_index)==paste(year_to_start,'01',sep='-')):length(unique(df_rend2$year_month_index))]
  start.period <-  initial.periods[seq(1,length(initial.periods),by=rebalance_period)]
  final.period <- final.periods[seq(1,length(final.periods),by=rebalance_period)]
  # initial values
  df_re_all_years <- NULL
  df_sd_all_years <- NULL
  df_min.ret.weights <- NULL
  df_eqw.ret.weights <- NULL
  df_ran.ret.weights <- NULL
  df_cum_return <- NULL
  re.port <- NULL
  sd.port <- NULL
  matCov <- NULL
  for (i in 1:length(final.period)){
    date_min <- start.period[i]
    date_max <- final.period[i]
    # estimate the number of days 
    days_next_month <- as.numeric(sum(!weekdays(seq(seq(as.Date(paste(date_max,'-01',sep='')), by = "month", length = 3)[2], 
                                                    seq(as.Date(paste(date_max,'-01',sep='')), by = "month", length = 3)[3]-1, "days")) %in% c("s�bado", "domingo") ))
    
    # filter by max_date
    base_roll <- df_rend2 %>%
      filter(year_month_index >= date_min & year_month_index < date_max) %>%
      dplyr::select(-year,-month,-year_month_index)
    
    # selecting the best k stocks
    base_roll_top <- top_n(returns=base_roll, sorted_by=sorted, top=top.k)
    # print iterations
    cat(' Stocks selected = ',colnames(base_roll_top[-1]), "\n")
    # parameters
    mat.cov_roll2 <- mat_cov2(base_roll=base_roll_top, type=mod, n.ahead=days_next_month)
    matCov <- abind(matCov, mat.cov_roll2, along=3)
    # sd and re
    sd_roll <- sqrt(diag(mat.cov_roll2))
    r.e_roll <- colMeans(base_roll_top[,-1])
    # get min porfolio
    port.min<-getMinPortfolio(r.e_roll, mat.cov_roll2) 
    # weights
    w_min <- port.min$pesos
    w_eqw <- rep(1/length(base_roll_top[,-1]),length(base_roll_top[,-1]))
    names(w_eqw) <- names(w_min)
    w_rand <- random_weights(ncol(base_roll_top[,-1]))
    names(w_rand) <- names(w_min)
    #  weights matched
    min.ret.weights <- all_weights(base=df_rend, w_min)
    eqw.ret.weights <- all_weights(base=df_rend, w_eqw)
    ran.ret.weights <- all_weights(base=df_rend, w_rand)
    # cummulative weights
    df_min.ret.weights <- rbind(df_min.ret.weights,min.ret.weights)
    df_eqw.ret.weights <- rbind(df_eqw.ret.weights,eqw.ret.weights)
    df_ran.ret.weights <- rbind(df_ran.ret.weights,ran.ret.weights)
    # total portfolio base
    if(i < length(final.period)){
      base_total_port <- df_rend2 %>%
        filter(year_month_index >= final.period[i] & year_month_index < final.period[i+1]) %>%
        dplyr::select(-year,-month,-year_month_index) 
    } else{
      base_total_port <- df_rend2 %>%
        filter(year_month_index >= final.period[i] & Fecha < max(Fecha)) %>%
        dplyr::select(-year,-month,-year_month_index) 
    }
    # df of total portfolio
    df_cum <- 
      data.frame('date' = base_total_port[,1],
                 'min.ret' = getPortfolioReturns(base_total_port,w_min),
                 'eqw.ret' = getPortfolioReturns(base_total_port,w_eqw),
                 'ran.ret' = getPortfolioReturns(base_total_port,w_rand))
    # cummulative portfolio
    df_cum_return <- rbind(df_cum_return, df_cum)
    
    cat(paste('Estimated period : ', date_max,sep=''),"\n")
    
  }
  # df weights
  df_min_weights <- data.frame('year' = final.period, df_min.ret.weights)
  df_eqw_weights <- data.frame('year' = final.period, df_eqw.ret.weights)
  df_ran_weights <- data.frame('year' = final.period, df_ran.ret.weights)
  all <- list('df_min_weights' = df_min_weights,
              'df_eqw_weights' = df_eqw_weights,
              'df_ran_weights' = df_ran_weights,
              #'df_re_sd.port' = df_re_sd.port,
              'df.port.ret' = df_cum_return,
              'matCov' = matCov)
  return(all)
  
}
################################################################################

