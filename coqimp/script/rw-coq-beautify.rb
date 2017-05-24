#!/usr/bin/env ruby

##
# This script comments all the commands of a Coq file, which printing auxiliary information and is useless for public version.
# For example, there commands:
#   SearchAbout ".".
#   Print OSInv.
#   Locate ProgSim.
# will all be commented.
# SearchAbout ".". is commented to (** * ac: SearchAbout ".". *).

# Use of this script:
#   ./rw-coq-beautify FILE-or-DIR1 FILE-or-DIR2 ...
# If FILE-or-DIR is a coq file (*.v), then comments what we need in it.
# If FILE-or-DIR is a dir, then find all coq file (*.v) recursive, and perform operation on them.
# For example,
#   ./rw-coq-beautify .
# will comment all the auxiliary commands in current directory recursively.
# It also prints messages in the form:
#   file-name :
#    line-number: before -> after        
#    ...
# before is the initial text of commands in file, and after is the new text of commented text in file.

require 'fileutils'
require 'tempfile'

search_keywords = %w(Search Print Check Locate Show Eval)
REG = Regexp.new("^[[:blank:]]*" + "(" + search_keywords.join("|") + ")" + ".*[.]")
REG_TIME = /^([[:blank:]]*)Time[[:blank:]]+(.*[.])/ # special case, need to replace "Time command" by "command"

def coq_beautify (path)
  name = path.split("/").last
  unless name =~ /^[A-z0-9]+.*[.]v$/
    return
  end
  temp_file = Tempfile.new('foo')
  begin
    File.open(path, 'r') do |file|
      modify = false 
      file.each_line do |line|
        if (line =~ REG) or (line =~ REG_TIME) then
          unless modify then
            puts "#{file.path} :"
            modify = true
          end
          puts " #{$.}: #{line.chop} ->"
          if line =~ REG 
            line.sub!(REG){ |a| "(* ** ac: " + $& + " *)"}
          else
            line.sub!(REG_TIME) { |matched| $1 + $2 }
            # { |blank, command| blank.to_s + command.to_s }
          end
          puts "   #{line.chop}"
        end
        temp_file.puts line
      end
      temp_file.close
      FileUtils.mv(temp_file.path, path)
    end
  ensure
    temp_file.close
    temp_file.unlink
  end
end

def traverse (path)
  if File.directory?(path)
    dir = Dir.open(path)
    while name = dir.read
      next if name == "."
      next if name == ".."
      traverse(path + "/" + name)
    end
  else
    coq_beautify(path)
  end
end

ARGV.each do |path|
  traverse(path)
end

