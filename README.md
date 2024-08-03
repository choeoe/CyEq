# CyEq: Proving the Cypher Query Equivalence 

## Introduction

CyEq is a tool designed to prove the equivalence of Cypher queries in graph
databases. This tool helps users ensure that different Cypher queries return the
same results, which is essential for optimization and reliability checking in graph
database systems.

## Requirements

To run CyEq, ensure your system meets the following requirements:

- **Java Development Kit (JDK)**: Version 17
- **Maven**: Version 3.8 or higher
- **ubuntu**: 1804

## Installation

1. **Clone the repository**:

    ```sh
    git clone https://github.com/choeoe/CyEq.git
    cd CyEq
    ```

2. **Build the project using Maven and run**:

    ```sh
    mvn clean package
    cd dataset
    java -Djava.library.path=./ -cp CyEQ-1.0-SNAPSHOT-jar-wi-dependencies.jar:z3/com.microsoft.z3.jar cyeq.Main
    ```

3. **Or run the application using our script**:

    ```sh
    Bash run.sh
    ```

## Usage

To use CyEq, follow these steps:

1. **Prepare your queries**: Write the Cypher queries you want to compare into /dataset/dataset.xlsx.
2. **Run CyEq with the queries**:

    if you have compiled the project:
    ```
    cd dataset
    java -Djava.library.path=./ -cp CyEQ-1.0-SNAPSHOT-jar-wi-dependencies.jar:z3/com.microsoft.z3.jar cyeq.Main
    ```
    otherwise
    ```sh
    Bash run.sh
    ```

3. **Review the results**: CyEq will write the verification result back into the
   dataset. Please check the result at the end of the Cypher query pair. Note
   that if a Cypher query pair is proven NQE, it still might be equivalent,
   since CyEq is incomlete.

## Test Data

CyEq includes a set of test data for evaluating the tool's effectiveness. The
test data consists of 145 equivalent Cypher queries to ensure comprehensive
coverage of different query structures and graph patterns.

### Example Test Dataset

- **CyEqBench ver 1**: The dataset is in /dataset/dataset.xlsx, which contains 145 equivalent Cypher query pairs
  from:
    + translation from Calcite.
    + transformation from real-word Cypher queries.


