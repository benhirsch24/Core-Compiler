for file in *; do
   if [ -d $file ]; then
      cd $file;
      for coref in *.core; do
         ../../Core $coref > $coref.out
      done
      cd ..;
   fi
done

