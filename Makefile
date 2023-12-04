library: index
	lake build

index:
	lake script run updateIndex

clean:
	lake clean

all: index library
	lake script run updateDependencyMap pictures/dependency-map.svg
