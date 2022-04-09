hdmv <-
function(X, Y = NULL, mu = NULL, cov.equal = TRUE, l = NULL, kappa = NULL, type = "a1", 
                 linearcoef = NULL,  na.action = na.fail, ...) {
  hdmvformula <- function(formula, na.action = na.fail, ...) {
      if(missing(formula)
         || (length(formula) != 3)
         || (length(attr(terms(formula[-2]), "term.labels")) != 1))
        stop("'formula' missing or incorrect")
      m <- match.call(expand.dots = FALSE)
      if(is.matrix(eval(m$data, parent.frame())))
        m$data <- as.data.frame(data)
      m[[1]] <- as.name("model.frame")
      m$... <- NULL
      mf <- eval(m, parent.frame())
      DNAME <- paste(names(mf), collapse = " by ")
      names(mf) <- NULL
      response <- attr(attr(mf, "terms"), "response")
      g <- factor(mf[[-response]])
      if(nlevels(g) != 2)
        stop("grouping factor must have exactly 2 levels")
      DATA <- split(as.data.frame(mf[[response]]), g)
      names(DATA) <- c("X", "Y")
      X <- DATA$X
      Y <- DATA$Y
      out <- list(X=X,Y=Y)
      return(out)
    }
  if(rlang::is_formula(X)) {
    formula <- X
    out <- hdmvformula(formula)
    X <- out$X
    Y <- out$Y 
  }
  
  if(!all(sapply(X, is.numeric))) stop("'X' must be numeric")
  X <- na.action(X)
  X <- as.matrix(X)
  p <- ncol(X)
  if (is.null(kappa)) kappa <- sqrt(p/log(p))
  
  
  if (!is.null(Y))
  {
    Y <- na.action(Y)
    Y <- as.matrix(Y)
    if(!all(sapply(Y, is.numeric))) stop("'Y' must be numeric")
    if (p != ncol(Y)) stop("'X' and 'Y' must have the same number of columns")
  }
  
  checkmean <- FALSE
  if (is.null(mu)) {
    mu <- numeric(p)
    checkmean <- TRUE
  }
  
  if (!is.null(mu) & (all(mu == 0))) {
    mu <- numeric(p)
    checkmean <- TRUE
  }
  
  if (length(mu) != p) stop("length of 'mu' must equal the number of columns of 'X'")
  
  myfunc <- function(v1) {
    deparse(substitute(v1))
  }
  
  if (is.null(Y)) 
  {
    DNAME = myfunc(X)
  }
  else
  {
    DNAME=paste(myfunc(X),"and",myfunc(Y))
  }
  if (is.numeric(type) & (length(type) != p) ) stop("the length of type should be equal to p")
  
  if (is.null(linearcoef)) {
    linear_coef <- switch (type,
                    "a1" = c(1, numeric(p-1)),
                    "a2" = c(rep(sqrt(floor(p/2))/floor(p/2), floor(p/2)),numeric(p-floor(p/2))),
                    "a3" = rep(sqrt(p)/p,p)
                    )
  }
  
  if (!is.null(linearcoef) & sqrt(sum(linearcoef^2)) != 1) stop("the norm of linearcoef shoud equal to 1")
  if (!is.null(linearcoef) & sqrt(sum(linearcoef^2)) == 1) linear_coef <- linearcoef
  
  
  tr = function(x){
    x_sumcol <- matrix(colSums(x), n, p, byrow = TRUE)
    
    q1 <- x_sumcol - x
    q2 <- tcrossprod(x, x) 
    diagq2 <- diag(q2)
    A1 <- sum(colSums(x * q1))
    A2 <- (sum(colSums(q2 * q2)) - (q3 <- sum(diagq2^2)))
    A3 <- (sum(colSums(q2 * tcrossprod(x, q1))) - sum(diagq2 * (q4 <- colSums(t(q1) * t(x)))))
    A4 <- (sum(diagq2 * colSums(t(x) * t(x_sumcol))) - q3)
    A5 <- sum(q4 * colSums(t(q1) * t(q1)))
    
    temp1 <- (n - 1) * n
    temp2 <- (n - 2) * temp1
    temp3 <- (n - 3) * temp2
    
    tr_est <- (q5 <- sum(diagq2))/n - A1/temp1
    tr2_est <- (A2/temp1 - (A3 - A4) * 2/temp2 + (A5 - 2 * A3 + 3 * A4 - A1 * q5)/temp3)
    
    return(list(tr_est = tr_est, tr2_est = tr2_est))
  }
  
  HDmv.one <- function(x, mu, linear_coef, kappa, l) { ## mu is a p dimensional vector
    x_mu  <- x - matrix(mu, n, p, byrow = TRUE) ## to be checked
    
    # Theorem 1
    temp0 <- sum( (q1 <- colMeans(x_mu))^2 ) 
    a     <- l/sqrt( temp0 + kappa * abs(sum(linear_coef * q1))^2 )
    xi    <- (n + 2)/(1 + a)
    temp1 <- sqrt( 1 + n * xi^2/(n + 2) )
    ## W formula (5) of Cui et al. (2020)
    W <- (-2*(n * log(1 + (1 - temp1)/n) + log(0.5 + 0.5 * xi + 0.5 * temp1) + log(0.5 - 0.5 * xi + 0.5 * temp1)))
    
    temp2  <- tr(x)
    q2 <-  cov(x)
    q3 <- sum(q2) 
    temp21 <- (temp2$tr_est  + kappa * q3 / p)
    temp22 <- (temp2$tr2_est + 2 * kappa * sum( q2 %*% q2 / p) + (kappa^2) * (q3/p)^2)
    ## tn formula (6 ) of Cui et al. (2020)
    Tn <- ( 2 * n * (l^2) * W/(n + 2)^2 - temp21 )/sqrt(2 * (temp22))
    #Tn_P <- pnorm(Tn, lower.tail = FALSE) * (Tn >= 0)  + pnorm(Tn, lower.tail = TRUE) * (Tn < 0) 
    Tn
  }
  
  trD = function(x, D){
    # x is n*p matrix
    nn <- nrow(x)
    # p <- ncol(x)
    x_sumcol <- matrix(colSums(x), nn, p, byrow = TRUE)
    q1 <- x_sumcol - x
    q2 <- x%*%D
    q3 <- q2%*%t(x)
    diagq3 <- diag(q3)
    
    A1 <- sum(colSums(q2 * q1))
    A2 <- (sum(colSums(q3 * q3)) - (q4 <- sum(diagq3^2)))
    A3 <- (sum(colSums(t(q3) * (q5 <- q1 %*% t(q2)))) -  sum(diagq3 * (q6 <- diag(q5))))
    A4 <- (sum(diagq3 * colSums(t(x) * (D%*%t(x_sumcol)))) - q4)
    A5 <- sum(q6 * colSums(t(q1) * (D%*%t(q1))))
    
    temp1 <- (nn - 1) * nn
    temp2 <- (nn - 2) * temp1
    temp3 <- (nn - 3) * temp2
    
    trD_est <- ((q7 <- sum(diagq3))/nn - A1/temp1)
    tr2D_est <- (A2/temp1 - (A3 - A4) * 2/temp2 + (A5 - 2 * A3 + 3 * A4 - A1 * q7)/temp3)
    
    traceD <- c(trD_est = trD_est, tr2D_est = tr2D_est)
    
    traceD
  }
  
  trD.mix = function(x1, x2, D){
    x_sumcol1 <- matrix(colSums(x1), n1, p, byrow = TRUE)
    x_sumcol2 <- matrix(colSums(x2), n2, p, byrow = TRUE)
    
    A1 <- D %*% t(x1) %*% x1
    A2 <- D %*% t(x_sumcol1-x1) %*% x1
    
    A3 <- D %*% t(x2) %*% x2
    A4 <- D %*% t(x_sumcol2-x2) %*% x2
    
    temp1 <- n1 * (n1 - 1)
    temp2 <- n2 * (n2 - 1)
    
    sigma1_est <- A1/n1 - A2/temp1
    sigma2_est <- A3/n2 - A4/temp2
    
    sum(colSums(t(sigma1_est) * sigma2_est))
  }
  
  HDmv.same <- function(X1, X2, linear_coef, kappa){
    
    ## X1 and X2 are n1*p and n2*p matrix
    
    k <- sqrt(p/log(p))
    I <- diag(p)
    D <- I + kappa * outer(linear_coef, linear_coef)
    
    
    tau <- (n1 + n2)/(n1 * n2)
    X1bar <- colMeans(X1)
    X2bar <- colMeans(X2)
    
    ##' 
    ##' proposed projection test for D
    ##' 
    
    #Tnew <- t(X1bar - X2bar) %*% D %*% (X1bar - X2bar)
    Tnew <- sum(colSums((X1bar - X2bar) *D) * (X1bar - X2bar))
    temp1 <- trD(X1,D)
    temp2 <-  trD(X2,D)
    trD_sigma <- (temp1[1] + temp2[1])/2
    trD_sigma2 <- (temp1[2] + temp2[2])/2
    Tn <- (Tnew - tau * trD_sigma) / (tau * sqrt(2 * trD_sigma2))
    #Tn_P <- pnorm(Tn, lower.tail = FALSE) * (Tn >= 0)  + pnorm(Tn, lower.tail = TRUE) * (Tn < 0) 
    
    Tn
  }
  
  HDmv.diff <- function(X1, X2, linear_coef, kappa){
    I <- diag(p)
    D <- I + kappa * outer(linear_coef, linear_coef)
    
    tau <- (n1 + n2)/(n1 * n2)
    X1bar <- colMeans(X1)
    X2bar <- colMeans(X2)
    
    ##'
    ##'  proposed projection test
    ##' 
    Tnew <- sum(colSums((X1bar - X2bar) *D) * (X1bar - X2bar))
    trD_est1 <- trD(X1,D)
    trD_est2 <- trD(X2,D)
    trD.mix_est <- trD.mix(X1,X2,D)
    trD_sigma <- trD_est1[1]/n1 + trD_est2[1]/n2
    trD_sigma_squre <- (2/n1^2 * trD_est1[2] 
                        + 2/n2^2 * trD_est2[2]
                        + 4/n1/n2 * trD.mix_est)
    
    Tn <- (Tnew - trD_sigma)/(sqrt(trD_sigma_squre))
    #Tn_P <- pnorm(Tn,lower.tail = FALSE) * (Tn >= 0)  + pnorm(Tn,lower.tail = TRUE) * (Tn < 0) 
    Tn
  }
  
  if ( is.null(Y) ) {
    n <- nrow(X)
    if (p < n) stop("p should be greater than or equal to n")
    if (is.null(l)) l <- n^(5/4)*log(n)
    statistic <- HDmv.one(X, mu, linear_coef, kappa, l) 
    p.val <- 2*pnorm(-abs(statistic))
    method <- "One sample projection test"
    out <- list(statistic = statistic, p.value = p.val, method = method, size = n)
  }
  
  if ( cov.equal & !is.null(Y) ) {
    n1 <- nrow(X)
    n2 <- nrow(Y)
    n <- n1 + n2 - 2
    if ( (p < n1) | (p < n2) ) stop("p should be greater than or equal to both n1 and n2")
    statistic <- as.numeric( HDmv.same(X, Y, linear_coef, kappa) )
    p.val <- 2*pnorm(-abs(statistic))
    method <- "Two sample projection test"
    out <- list(statistic = statistic, p.value = p.val, method = method, 
                size1 = n1, size2 = n2)
  }
  
  if ( !cov.equal & !is.null(Y) ) {
    n1 <- nrow(X)
    n2 <- nrow(Y)
    n <- n1 + n2 - 2
    if ( (p < n1) | (p < n2) ) stop("p should be greater than or equal to both n1 and n2")
    statistic <- as.numeric( HDmv.diff(X, Y, linear_coef, kappa) )
    p.val <- 2*pnorm(-abs(statistic))
    method <- "Two sample projection test"
    out <- list(statistic = statistic, p.value = p.val, method = method, 
                size1 = n1, size2 = n2)
  }
  
  out <- c(out, list(data.name = DNAME, alternative = "two.sided", checkmean = checkmean))
  class(out)<-"hdmv"
  printhdmv <-
    function(x, ...) {
      cat("\n")
      cat("   ",format(x$method, justify = "left"),"\n\n")
      cat("data: ", x$data.name,"\n")
      if(x$method == "One sample projection test") {
        cat(paste("statistic = ", round(x$statistic, 5),", n = ",x$size,", p-value = ", round(x$p.value,5),sep = ""),"\n")
        if(x$checkmean)
          cat("alternative hypothesis: ", "true mean is not equal to the origin \n")
        else cat("alternative hypothesis: ", "true mean is not equal to the specified mean (mu)\n")
      }
      if(x$method == "Two sample projection test") {
        cat(paste("statistic = ", round(x$statistic, 5),", n1 = ",x$size1,  ", n2 = ",x$size2, ", p-value = ",
                  round(x$p.value,5), sep = ""),"\n")
        cat("alternative hypothesis: ", "true mean vectors  are different\n")
      }
    }
  printhdmv(out)
  return(out)
}

 # g <- factor(rep(c(1,2),each=4))
 # XX=matrix(1:20,4,5)
 # df = rbind(XX,XX)
 # p <-ncol(XX)
 # linear_coef <- numeric(p)
 # linear_coef[2]<-1
 # kappa <- sqrt(p)/p
 # hdmv(X=XX,Y=XX,cov.equal = FALSE,linearcoef = linear_coef,kappa=kappa)
 # 
 # hdmv(df~g,kappa=kappa,cov.equal = FALSE,linearcoef = linear_coef)
