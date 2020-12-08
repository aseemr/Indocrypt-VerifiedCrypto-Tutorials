# Tamarin

The Tamarin prover provides a server, to which we can connect using a web browser (e.g. as Firefox or Chrome).

There are several options for installing Tamarin.

## Option 1: Install for your own platform

For many platforms we provide dedicated installation instructions here:

  * [Tamarin manual installation instructions](https://tamarin-prover.github.io/manual/book/002_installation.html)

After that, you can start the Tamarin prover with the files in the current directory:

  `tamarin-prover interactive .`

## Option 2: Use Docker

```
docker build -t tamarin
mkdir tamarin
chmod a+rwx tamarin
docker run -t --publish 3001:3001 --volume $(pwd)/tamarin:/workspace tamarin
```

This should start the Tamarin prover in a Docker instance, and you can then point your browser at the URL that it should show: 127.0.0.1:3001.

