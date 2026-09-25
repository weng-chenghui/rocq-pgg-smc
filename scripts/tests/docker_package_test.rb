#!/usr/bin/env ruby

dockerfile = File.read(ARGV.fetch(0))

required = [
  "FROM mathcomp/mathcomp@sha256:",
  "ARG SOURCE_REVISION",
  "ARG ROCQ_JOBS=1",
  "org.opencontainers.image.source",
  "org.opencontainers.image.revision",
  'make -f Makefile.rocq -j"${ROCQ_JOBS}"',
  "make -f Makefile.rocq install"
]
missing = required.reject { |fragment| dockerfile.include?(fragment) }
raise "missing Dockerfile text: #{missing.join(", ")}" unless missing.empty?

compile_index = dockerfile.index('make -f Makefile.rocq -j"${ROCQ_JOBS}"')
install_index = dockerfile.index("make -f Makefile.rocq install")
cmd_index = dockerfile.index("CMD")
raise "compile must precede install" unless compile_index < install_index
raise "installation must finish before CMD" unless install_index < cmd_index

cmd_text = dockerfile.lines.drop_while { |line| !line.start_with?("CMD") }.first
raise "container startup must not compile" if cmd_text&.include?("make")

puts "docker_package_test: PASS"
