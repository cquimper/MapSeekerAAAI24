#!/bin/bash
#SBATCH --time=168:0:00
#SBATCH --account=def-cquimper
#SBATCH --mem-per-cpu=10G
#SBATCH --array=1-510
#SBATCH --output=data6_00_w_decomp/jobs_1/job_%a.out
eval ./gen_paralle_conj.sh `awk "NR==$SLURM_ARRAY_TASK_ID" data6_00_w_decomp/jobs_1/threads_1.tex`
