FROM python
RUN curl -LO "https://dl.k8s.io/release/$(curl -L -s https://dl.k8s.io/release/stable.txt)/bin/linux/amd64/kubectl"
RUN mkdir -p ~/.local/bin/kubectl && mv ./kubectl ~/.local/bin/kubectl && chmod +x ~/.local/bin/kubectl/kubectl
ENV PATH="~/.local/bin/kubectl:${PATH}"
RUN yes w | pip install gunicorn flask bootstrap-flask flask-wtf flask-login flask_sqlalchemy psycopg2 wtforms kubernetes passlib argon2-cffi
COPY . /kubeApp
WORKDIR /kubeApp
ENV FLASK_APP=app.py
ENTRYPOINT ["gunicorn"]
CMD ["--threads=3", "-w 10", "-b 0.0.0.0:5000", "app:app"]
