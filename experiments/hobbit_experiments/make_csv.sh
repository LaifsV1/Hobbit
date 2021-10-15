BFSE=bfs_equiv.txt
BFSI=bfs_inequiv.txt
DFSE=dfs_equiv.txt
DFSI=dfs_inequiv.txt

DEF=default
NS=no_sep
#NR=no_reuse
NE=no_reentry
NG=no_gen
NA=no_all

F=files_
T=err_
S=status_

run_paste () {
    echo "	default		no sep		no reentry		no gen		no all	" > $1.csv
    echo "filename	times	eq	times	eq	times	eq	times	eq	times	eq" >> $1.csv
    paste $DEF/$F$1 $DEF/$T$1 $DEF/$S$1 $NS/$T$1 $NS/$S$1 $NE/$T$1 $NE/$S$1 $NG/$T$1 $NG/$S$1 $NA/$T$1 $NA/$S$1 >> $1.csv
}

run_paste $BFSE
run_paste $BFSI
#run_paste $DFSE
#run_paste $DFSI

