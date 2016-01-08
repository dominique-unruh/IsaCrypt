FROM unruh/isabelle:multivariate2015
ADD ROOT ROOT
RUN isabelle build -d . -b IsaCrypt-Prereqs && ~/set-logic IsaCrypt-Prereqs && rm ROOT
