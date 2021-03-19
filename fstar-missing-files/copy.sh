prefix="/home/lucas/FStar/"

cd "$prefix/src/basic/boot/"
for i in FStar.*.fsi; do
    cat "$i" | grep -v "// JUST FSHARP" | sed 's/^\/\/ IN F\*: //' > "$prefix/fstar-missing-files/$i"
done
