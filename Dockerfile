# Wir nutzen ein offizielles Python-Image als Basis
FROM python:3.11-slim

# Installiere System-Abhängigkeiten, die für Geodaten-Bibliotheken nötig sind
RUN apt-get update && apt-get install -y \
    gcc \
    g++ \
    gdal-bin \
    libgdal-dev \
    libproj-dev \
    proj-bin \
    && rm -rf /var/lib/apt/lists/*

# Arbeitsverzeichnis im Container erstellen
WORKDIR /app

# Kopiere die requirements und installiere die Python-Pakete
COPY Docker/requirements.txt ./requirements.txt
RUN pip install --no-cache-dir --upgrade pip \
    && pip install --no-cache-dir -r requirements.txt

# Kopiere den Projektcode in den Container
COPY . .

# Starte das Skript
CMD ["python", "Nutzbar/API_LVS95.py"]
