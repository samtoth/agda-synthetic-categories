echo "module Everything where" > src/Everything.agda

find src -type f -name '*.lagda.tree' | \
  grep -v "Everything" | sort | \
  sed -re 's@src/@@g;s@.lagda.tree@@g;s@/@.@g;s@^@open import @g;s@$@@g' \
  >> src/Everything.agda

find src -type f -name '*.agda' | \
  grep -v "Everything" | sort | \
  sed -re 's@src/@@g;s@.agda@@g;s@/@.@g;s@^@open import @g;s@$@@g' \
  >> src/Everything.agda
