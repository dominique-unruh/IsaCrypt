FROM unruh/isabelle:pure
USER root
RUN echo '/^ISABELLE_LOGIC=/c\nISABELLE_LOGIC=HOL\n.\nw\nq' | ed -s /opt/Isabelle2015/etc/settings 
USER user
RUN isabelle build -b HOL
