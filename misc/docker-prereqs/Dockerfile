FROM unruh/isabelle:multivariate

USER root
RUN echo '/^ISABELLE_LOGIC=/c\nISABELLE_LOGIC=IsaCrypt-Prereqs\n.\nw\nq' | ed -s /opt/Isabelle2015/etc/settings 
USER user

ADD ROOT ROOT
RUN isabelle build -b -d . IsaCrypt-Prereqs
RUN rm ROOT
