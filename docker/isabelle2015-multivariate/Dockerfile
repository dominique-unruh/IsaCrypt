FROM unruh/isabelle:hol
USER root
RUN echo '/^ISABELLE_LOGIC=/c\nISABELLE_LOGIC=HOL-Multivariate_Analysis\n.\nw\nq' | ed -s /opt/Isabelle2015/etc/settings 
USER user
RUN isabelle build -b HOL-Multivariate_Analysis
