\name{hdmv}
\alias{hdmv}
%- Also NEED an '\alias' for EACH other topic documented here.
\title{
High-dimensional mean vector(s) test
}
\description{
\code{hdmv} function allows a high dimensional test for the one and two-sample mean vector(s) hypothesis problem, where the dimension p (number of variables)  is large than the sample size n (number of individual).
}
\usage{
hdmv(X, Y = NULL, mu = NULL, cov.equal = TRUE, l = NULL, kappa = NULL, type = "a3", linearcoef = NULL, na.action = na.fail, ...)
}
%- maybe also 'usage' for other objects documented here.
\arguments{
  \item{X}{
a numerical n_X*p  data frame or matrix.
}
  \item{Y}{
an optional numerical n_Y*p data frame or matrix,for the two-sample high dimensional mean vectors test. If NULL, a one-sample high dimensional mean vector test is supplied.
}
  \item{mu}{
a vector indicating the hypothesized value of the mean.   If NULL the origin or a two-sample test is supplied.
}
  \item{cov.equal}{
logical. If TRUE (default) the statistic test using  identical covariance matrix of two samples is supplied. Otherwise, the test for different covariance matrix of  two samples are is used.
}
  \item{l}{
a positive constant. If NULL, the default value \code{l=n^(5/4) log(n)} is used or the two-sample  mean vectors test is performed.  See \code{Details}.
}
  \item{kappa}{
a positive constant. If NULL, the default value \code{kappa =  sqrt(p/log(p))} is used.  See \code{Details}. 
}
  \item{type}{
a different option of linear coefficient \code{linearcoef}. There are currently three options of linear coefficients \code{linearcoef}.  The options are  "a1", "a2"  and "a3". If NULL the default optionl "a3" is performed. The specific values are given in \code{Details}.
}
  \item{linearcoef}{
an optional numeric p-unit vector. If NULL \code{type} is automatically supplied.
}
  \item{na.action}{
a generic function deals with \code{NA}s in e.g., data frame or matrix.  If \code{na.fail} (default) the object if it does not contain any missing value is returned. Otherwise, an error is returned. If \code{na.omit} the object with incomplete data frame or matrix, which is removed the row with \code{NA}s value  is returned.
}
  \item{\dots}{
%%     ~~Describe \code{\dots} here~~
}
}
\details{
 The powerful high dimensional test for testing the specific mean vector or for testing the equality of two mean vectors with identical or different covaraince matrices.Two high dimensional hypothesis testing are an empirical likelihood ratio test for one sample problem (Cui et al., 2020),  and a projection test for two-sample problem (Huang et al. 2022). Two testing approaches are both more powerful than that of their competitors, such as Bai and Saradarara (1996) and Chen and Qin (2010).

 \code{l} argument is constrained on the condition which l^(-1)*n^(5/4) tends to 0. See Cui et al. (2020) for more details.
 
 
 \code{kappa} argument is constrained on the condition which kappa / sqrt(p) tends to 0. See Cui et al. (2020) and Huang et al. (2022) for more details.

The type of linear coefficient to be used is specified through the
 \code{type} argument (see \code{\link{hdmv}} for details).

The available options are:

 \itemize{
 \item \code{type = "a1"}: a unit p-vector with first element 1 and 0 otherwise, i.e. (1, 0_{p-1}), where 0_{p-1} denotes a p-1 vector of zeroes;
 \item \code{type = "a2"}: a unit p-vector with first ceiling half elements sqrt(ceiling(p/2))/ceiling(p/2) and 0 otherwise; i.e. ( sqrt(ceiling(p/2))/ceiling(p/2) * 1_(ceiling(p/2)), 0_(p-ceiling(p/2)) );
 \item \code{type = "a3"}:  a unit p-vector with each element sqrt(p)/p; i.e. sqrt(p)/p 1_p, where 1_p denotes a p vector of ones. 
 }
}
\value{
A  list with class \code{hdmv} includes the following components:
\itemize{
 \item \code{method} a character string indicating what type of test is performed.
\item \code{data.name} a character string giving the name of the data.
 \item \code{statistic} the value of the empirical likelihood ratio statistic or projection statistic, with 5 digits.
 \item \code{sample size} the sample size(s) of the data.
 \item \code{p-value} the p-value for the test, with 5 digits.
 \item \code{null.value} the specified hypothesized value of the mean depending on whether it was a one-sample test.
 \item \code{alternative} a character string with the value "two.sided".
 }
}
\references{
 Cui X., Li R., Yang G. and Zhou W. (2020), Empirical likelihood test for a large-dimensional mean vector, Biometrika, 107(3), 591-607, https://doi.org/10.1093/biomet/asaa005


 Huang C., Kenne Pagui E.C. and Cui X. (2022). Two-sample mean vector projection test in high-dimensional data.
 Submitted paper.

}
\author{
Caizhu Huang [aut, cre] \email{caizhu.huang@phd.unipd.it}, Euloge Clovis Kenne Pagui [aut, cre] \email{kenne@stat.unipd.it}, Xia Cui [aut] \email{cuixia@gzhu.edu.cn}
}
\note{
%%  ~~further notes~~
}

%% ~Make other sections like Warning with \section{Warning }{....} ~

\seealso{
%% ~~objects to See Also as \code{\link{help}}, ~~~
}
\examples{
## One-sample high dimensional mean vector test
library(mnormt)
p <- 100
n <- 50
varcov <- matrix(0.65, p, p)
diag(varcov) <- rep(1,p)
mu <- rnorm(p)
X <- rmnorm(n = n, mean = mu, varcov)
res1 <- hdmv(X = X) ## the test check if the true mean vector is zero 
res1$p.value
res2 <- hdmv(X = X, mu = mu) ## the test check if the true mean vector is equal to mu.
res2$p.value

# Two-sample high dimensional mean vector test
# Example in genetic data
library(simPATHy)
data(chimera)
group <- colnames(chimera)
X1 <- t(chimera[, group == 1])
X2 <- t(chimera[, group == 2])
n1 <- nrow(X1)
n2 <- nrow(X2)
p <- ncol(X1)


# Two-sample high dimensional mean vectors test
res_same <- hdmv(X = X1, Y = X2, cov.equal = FALSE)
res_diff <- hdmv(X = X1, Y = X2, cov.equal = TRUE)

# Using formula argument
g <- as.numeric(group)
df <- rbind(X1, X2)
res_same_f <- hdmv(df ~ g, cov.equal = FALSE)
res_diff_f <- hdmv(df ~ g, cov.equal = TRUE)

# Use one of the three default linear coefficients
res_same_a1 <- hdmv(X = X1, Y = X2, cov.equal = FALSE, type = "a1")
res_same_a2 <- hdmv(X = X1, Y = X2, cov.equal = FALSE, type = "a2")
res_same_a3 <- hdmv(X = X1, Y = X2, cov.equal = FALSE, type = "a3")

# Using a specific linear coefficient 
linear_coef <- c(rep(sqrt(ceiling(p/4))/ceiling(p/4), ceiling(p/4)), rep(0,p-ceiling(p/4)))
res_same_linear <- hdmv(X = X1, Y = X2, cov.equal = FALSE, linearcoef = linear_coef)

# Specific the constant kappa
kappa <- 2 * sqrt(p/log(p))
res_same_kappa <- hdmv(X = X1, Y = X2, cov.equal = FALSE, kappa = kappa)

}
% Add one or more standard keywords, see file 'KEYWORDS' in the
% R documentation directory (show via RShowDoc("KEYWORDS")):
% \keyword{ ~kwd1 }
% \keyword{ ~kwd2 }
% Use only one keyword per line.
% For non-standard keywords, use \concept instead of \keyword:
% \concept{ ~cpt1 }
% \concept{ ~cpt2 }
% Use only one concept per line.
