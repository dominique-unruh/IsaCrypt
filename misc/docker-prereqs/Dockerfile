FROM unruh/isabelle:multivariate2016
ADD ROOT ROOT
RUN isabelle build -d . -b IsaCrypt-Prereqs && ~/set-logic IsaCrypt-Prereqs && rm ROOT
