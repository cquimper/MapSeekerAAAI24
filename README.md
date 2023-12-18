README

## Data generation  
  
>The data generation phase includes in this order  
>1. the generation of a set of tables associated with each combinatorial object,  
>2. the generation of some metadata for each generated table associated with each combinatorial object,  
>3. the generation of some meta metadata for the metadata of each combinatorial object.  
  
  
  
### Generating the data, i.e. the tables, for the combinatorial objets graph, partition, partition0, group, cgroup.  
  
>Make sure that, within the directory containing the bound seeker code files, there is a directory called **data**, and make sure that with this **data** directory there are the directories called **graph**, **partition**, **partition0**, **group**, **cgroup**, **tree**, **forest**, and **forest0**.  
  
>For generating the graph data, i.e. the tables of the graph combinatorial object do:  
>1. Check that within the **/data/graph** directory we have the empty directories **data2, data3, ... , data26.**  
>2. Open a bash shell and position yourself in the directory containing the files of the **bound seeker**,  
>3. Run SICStus Prolog and run the goal `[gen_data].` to load the file `gen_data.pl`,  
>4. Type the goal `top(graph, 26, 1).`,  
>5. Type `halt.` to exit SICStus Prolog.  
  
>Proceed in a similar way to generate the tables of the _partition_, _partition0_, _group_, and _cgroup_ combinatorial objects, by respectively replacing `graph` by `partition`, `partition0`, `group`, and `cgroup`, and  
the constant `26` by `30`, `30`,`30` and `30`.  
  
>Note that for the _tree_, _forest_, and _forest0_ combinatorial objects, a python code generates the corresponding tables.  
  
  
  
### Generating the metadata associated with each table of the combinatorial objects graph, partition, partition0, group, cgroup, tree, forest, and forest0.  
  
>For generating the graph metadata do:  
>1. Open a bash shell and position yourself in the directory containing the files of the bound seeker,  
>2. Run SICStus Prolog and run the goal `[gen_metadata].` to load the file `gen_metadata.pl`,  
>3. Type the goal `top(graph, 26).`,  
>4. Type `halt.` to exit SICStus Prolog.  
  
>Proceed in a similar way to generate the metadata of the _partition_, _partition0_, _group_, _cgroup_, _tree_, _forest_, _forest0_ combinatorial objects, by respectively replacing `graph` by `partition`, `partition0`, `group`, `cgroup`, `tree`, `forest`, `forest0` and the constant `26` by `30`, `30`, `30`, `30`, `22`, `22`, and `22`.  
  
  
  
### Generating the meta metadata associated with each combinatorial objets graph, partition, partition0, group, cgroup, tree, forest, and forest0.  
  
>For generating the graph meta metadata do:  
>1. Open a bash shell and position yourself in the directory containing the files of the bound seeker,  
>2. Run SICStus Prolog and run the goal `[gen_meta_metadata].` to load the file `gen_meta_metadata.pl`,  
>3. Type the goal `top(graph, 26).`,  
>4. Type `halt.` to exit SICStus Prolog.  
  
>Proceed in a similar way to generate the metadata of the _partition_, _partition0_, _group_, _cgroup_, _tree_, _forest_, _forest0_ combinatorial objects, by respectively replacing `graph` by `partition`, `partition0`, `group`, `cgroup`, `tree`, `forest`, `forest0` and the constant `26` by `30`, `30`, `30`, `30`, `22`, `22`, and `22`. 

### How the generate the forest, forest0 and tree objects used in the experiment of decomposition method

> The files insides this directory are used to generate three combinatorials objects, namely :

1.  forest with isolated vertices noted _forest_
2.  forest without isolated vertices noted _forest0_
3.  tree noted _tree_

> The goal of thoses scripts is to generate instances (in SICStus prolog format) for three combinatorial objects where one of their characteristics are optimal acccording to their values. As examples of characteristics, we have the greatest depth of a node noted _maxp_, the number of leaves noted _f_ or the number of nodes noted _v_ and etc…

> The main method used to generate those objects is a dedicated algorithm of [Donald E. Knuth](https://www-cs-faculty.stanford.edu/~knuth/taocp.html) stated Algorithm O (_Oriented forest_) of his book titled _Art of Computer Programming, Volume 4, Fascicle 4, Generating All Trees, History of Combinatorial Generation_

### Command lines to generate the objects forest, forest0 and tree objects used in the experiment of decomposition method

#### Dependencies

> The programs [`python3`](https://www.python.org/downloads/) should be installed.


#### Preparation for running the files to generate the combinatorials objects.

  

> Upload on your computer the directory  __generate_data_forest_AAAI24__ and its contains avalaible in git repository.

  

### Running the program to generate the combinatorial objects

  

> To generate the combinatorial object __forest__, __forest0__, or __tree__, you just need  to respectively run in the Terminal from the repository __generate_data_forest_AAAI24__ the scripts below:
`python3 gen_forest.py maximum_size_of_the_combinatorial_object`
`python3 gen_forest0.py maximum_size_of_the_combinatorial_object`
`python3 gen_tree.py maximum_size_of_the_combinatorial_object`

### Results of running the scripts above

> After running the scripts above, the generated objects which have extremal values of their caracteristics and no more than `maximum_size_of_the_combinatorial_object` vertices are stored in the directory named _data_object_ where object is respectively _forest_, _forest0_, or _tree_.
> Then you copy those directories **forest, forest0, tree** in the **data** directory of the bound seeker.


## Instruction on how to reproduce the experiments executed on the clusters of  Digital Research Alliance of Canada to learn sharp bounds using decomposition methods



  

To reproduce the test performed on the clusters of  Digital Research Alliance of Canada perform the following steps:

  

### Running the 1rst version of the acquisition tool which use original biases  without  the 4 decompositions methods

  

>1. First upload on the cluster of Digital Research Alliance of Canada the version of Bound Seeker code files **which  do not use** decomposition methods. The code is at the archive repository.
>2. Upload the files `run_on_cluster.pl, cmds_for_maps.pl` and the directory __data6_00_wo_decomp__ in the same directory that contains the file `main.pl` of the version of Bound Seeker code files **which do not use** decomposition methods and that you previously uploaded on the cluster of Digital Research Alliance of Canada.
>3. Then open in edit option the code file `main.pl`  of the version of Bound Seeker code files **which  do not use** decomposition methods. At line number 608, change the name of the directory inside brackets `'data/',KindCombi,/found_conjectures_',FilesOutSuffix,'.pl'` by the name `'data6_00_wo_decomp/', KindCombi,'/found_conjectures_', FilesOutSuffix,'.pl'`. 
>Then record and close the file.
>4. From the terminal of cluster and inside the same directory of the file `main.pl`   run SICStus Prolog (version 4.6.0 or a more recent version)  with the following command to launch the experiments:
`| ?- [run_on_cluster], submit_job('6_00_wo_decomp'), halt.`

  

After launching the command above, **510  jobs** (a job is to find sharp bounds on a group of data bound table of the same characteristic of the same combinatorial object) to find sharp bounds **without the decomposition methods** will be launched where the maximum time of running is **one week**.

  

>5. After the jobs on clusters are finished, from the terminal of cluster and inside the same directory of the file `main.pl`  run SICStus Prolog (version 4.6.0 or a more recent version)  with the following command to get the results of the experiments:
`| ?- [run_on_cluster], get_results('6_00_wo_decomp'), halt.`



  

When the running of the command above terminates, you can access the results which are the conjectures files in the directory:
>**data6_00_wo_decomp/name_of_the_combinatorial_object_v6_00_wo_decomp/conjectures_name_of_the_combinatorial_object**

And you can access the results which are the formulae of the conjectures in the files
 >**data6_00_wo_decomp/name_of_the_combinatorial_object_v6_00_wo_decomp/results_name_of_the_combinatorial_object.tex**

where **name_of_the_combinatorial_object** is one of the following names of objects : **graph , partition, partition0, group, cgroup, tree, forest, forest0.**

  

  

  

  



### Running the 2nd version of the acquisition tool which use original biases  with  the 4 decompositions methods

  

>1. First upload on the cluster of Digital Research Alliance of Canada the version of Bound Seeker code files **which  use** decomposition methods. The code is at the archive repository.
>2. Upload the files `run_on_cluster.pl, cmds_for_maps.pl` and the directory **data6_00_w_decomp** in the same directory that contains the file `main.pl` of the version of Bound Seeker code files **which  use** decomposition methods and that you previously uploaded on the cluster of Digital Research Alliance of Canada.
>3. Then open in edit option the code file `main.pl`  of the version of Bound Seeker code files **which  use** decomposition methods. At line number 608, change the name of the directory inside brackets `'data/',KindCombi,/found_conjectures_',FilesOutSuffix,'.pl'` by the name `'data6_00_w_decomp/', KindCombi,'/found_conjectures_', FilesOutSuffix,'.pl'`. Then record and close the file.
>4. From the terminal of cluster and inside the same directory of the file `main.pl`   run SICStus Prolog (version 4.6.0 or a more recent version)  with the following command to launch the experiments:
`| ?- [run_on_cluster], submit_job('6_00_w_decomp'), halt.`

  

After launching the command above, **510  jobs** (a job is to find sharp bounds on a group of data bound table of the same characteristic of the same combinatorial object) to find sharp bounds without the decomposition methods will be launched where the maximum time of running is **one week.**

  

>5. After the jobs on clusters are finished, from the terminal of cluster and inside the same directory of the file `main.pl`  run SICStus Prolog (version 4.6.0 or a more recent version)  with the following command to get the results of the experiments:
`| ?- [run_on_cluster], get_results('6_00_w_decomp'), halt.`

When the running of the command above terminates, you can access the results which are the conjectures files in the directory:
>**data6_00_w_decomp/name_of_the_combinatorial_object_v6_00_w_decomp/conjectures_name_of_the_combinatorial_object**

And you can access the results which are the formulae of the conjectures in the files

>**data6_00_w_decomp/name_of_the_combinatorial_object_v6_00_w_decomp/results_name_of_the_combinatorial_object.tex**

where **name_of_the_combinatorial_object** is one of the following names of objects : **graph , partition, partition0, group, cgroup, tree, forest, forest0.**


## To reproduce results of the table 1 do:

>1.    In the terminal (or command line) directory to the version 1 of the tool, i.e. directory **ver1/**
    Copy the data folder in it. Execute the script file (as explained above).
Collect the generated files which contain conjectures into the directory 'ver2/conjecture_files/' replacing all the existing files there.
>2.    In the terminal (or command line) change directory to the version 2 of the tool, i.e. directory **ver2/**
    Copy the data folder in it. Execute the script file. (as explained above)
Collect the generated files which contain conjectures into the directory **ver2/conjecture_files_decomp/** replacing all the existing files there.
>3.    In the terminal (or command line) change directory to the version 2 of the tool, i.e. directory **ver2/**.
    Run SICStus Prolog from the terminal (version 4.6.0 or a more recent version) with the following command to print in the console the results:

`| ?- [decomposition_stats], create_stats, halt.`
