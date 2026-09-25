#!/usr/bin/env ruby

require "yaml"

workflow_path = ARGV.fetch(0)
workflow_text = File.read(workflow_path)
workflow = YAML.safe_load(workflow_text, aliases: false)

expected_trigger = {"push" => {"branches" => ["main"]}}
unless workflow.fetch("on") == expected_trigger
  raise "wrong trigger: #{workflow.fetch("on").inspect}"
end

expected_permissions = {"contents" => "read"}
unless workflow.fetch("permissions") == expected_permissions
  raise "wrong permissions: #{workflow.fetch("permissions").inspect}"
end

jobs = workflow.fetch("jobs")
unless jobs.keys == ["flattened-build"]
  raise "unexpected jobs: #{jobs.keys.inspect}"
end

job = jobs.fetch("flattened-build")
raise "wrong runner" unless job.fetch("runs-on") == "ubuntu-latest"

expected_container = {
  "image" => "mathcomp/mathcomp@sha256:ad95400eeb7f6fecb9d3b85673bf58990ae5800d9a8c41fd533e2f9678754cbc",
  "options" => "--user root",
  "env" => {"OPAMROOT" => "/home/rocq/.opam"}
}
unless job.fetch("container") == expected_container
  raise "wrong build container: #{job.fetch("container").inspect}"
end

uses = job.fetch("steps").map { |step| step["uses"] }.compact
expected_uses = [
  "actions/checkout@d23441a48e516b6c34aea4fa41551a30e30af803",
  "actions/upload-artifact@043fb46d1a93c77aae656e7c1c64a875d1fc6a0a",
  "actions/upload-artifact@043fb46d1a93c77aae656e7c1c64a875d1fc6a0a"
]
unless uses == expected_uses
  raise "wrong action references: #{uses.inspect}"
end

required_text = [
  "opam install . --deps-only --yes",
  "$GITHUB_SHA",
  "opam switch show --safe",
  "FLATTEN_JOBS=1",
  "source_archive_path",
  "built_archive_path",
  "-flat.tar.gz",
  "-built.tar.gz",
  "ulimit -s unlimited",
  "%ct",
  "date -u",
  "if-no-files-found: error"
]
missing = required_text.reject { |fragment| workflow_text.include?(fragment) }
raise "missing workflow text: #{missing.join(", ")}" unless missing.empty?

puts "flattened_build_workflow_test: PASS"
