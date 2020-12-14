# Tamarin

## Learning more about Tamarin

Tamarin has extensive documentation, theory and case study papers, teaching materials, and an active mailing list. Find out everything at the [Tamarin website](https://tamarin-prover.github.io/)!

## Running Tamarin

The Tamarin prover provides a server, to which we can connect using a web browser (e.g. as Firefox or Chrome).

There are several options for installing Tamarin.

### Option 1: Install for your own platform

For many platforms we provide dedicated installation instructions here:

  * [Tamarin manual installation instructions](https://tamarin-prover.github.io/manual/book/002_installation.html)

After that, you can start the Tamarin prover with the files in the current directory:

  `tamarin-prover interactive .`

If you unzip the examples in this directory, you can launch the tamarin prover in the relevant directory to immediately get a list of the protocol files inside.

### Option 2: Use Docker

```
docker build -t tamarin .
mkdir tamarin
chmod a+rwx tamarin
docker run -t --net=host --publish 3001:3001 --volume $(pwd)/tamarin:/workspace tamarin
```

This should start the Tamarin prover in a Docker instance, and you can then point your browser at the URL that it should show: 127.0.0.1:3001.

You can use the `Choose file` button to select any file ending in `.spthy`, and then click the `Load new theory` button to start working on the file.


