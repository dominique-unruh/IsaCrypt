FROM ubuntu

# Installing prerequisites
RUN apt-get -y update
RUN apt-get install -y lib32stdc++6 openjdk-7-jre wget ed

# Downloading and installing Isabelle
RUN wget https://isabelle.in.tum.de/dist/Isabelle2015_linux.tar.gz -O /tmp/Isabelle.tar.gz
RUN cd /opt && tar xf /tmp/Isabelle.tar.gz
RUN rm /tmp/Isabelle.tar.gz
RUN /opt/Isabelle2015/bin/isabelle install /usr/bin

# Create a user "user" and data directory (for mounting the host)
RUN useradd -m user
USER user
RUN mkdir /home/user/data
WORKDIR /home/user/data

# Sets the default logic to Pure
USER root
RUN echo '/^ISABELLE_LOGIC=/c\nISABELLE_LOGIC=Pure\n.\nw\nq' | ed -s /opt/Isabelle2015/etc/settings 
USER user
# Build Isabelle/Pure heap for user "user"
RUN isabelle build -b Pure


