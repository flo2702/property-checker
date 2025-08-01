package daikon;

import static java.nio.charset.StandardCharsets.UTF_8;
import static java.nio.file.StandardOpenOption.APPEND;
import static java.nio.file.StandardOpenOption.CREATE;

import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Paths;
import org.checkerframework.checker.initialization.qual.UnknownInitialization;

import edu.kit.kastel.property.subchecker.exclusivity.qual.*;

public class MemMonitor implements Runnable {

  boolean keep_going;
  long max_mem_usage;
  String filename;

  public @MaybeAliased MemMonitor(String filename) {
    this.filename = filename;
    try (PrintWriter fout = new PrintWriter(Files.newBufferedWriter(Paths.get(filename), UTF_8))) {

      keep_going = true;
      max_mem_usage = 0;

      long initial_mem_load = mem_usage();
      fout.println("Initial memory load, " + initial_mem_load);
      fout.println(
          "Format: pptName, peak_mem_usage, num_samples, num_static_vars, num_orig_vars,"
              + " num_scalar_vars, num_array_vars, num_derived_scalar_vars,"
              + " num_derived_array_vars");
    } catch (java.io.IOException e) {
      throw new Error("could not open " + filename, e);
    }
  }

  private long mem_usage(@UnknownInitialization(MemMonitor.class) MemMonitor this) {
    return (java.lang.Runtime.getRuntime().totalMemory()
        - java.lang.Runtime.getRuntime().freeMemory());
  }

  @Override
  public void run() {
    while (keep_going) {
      max_mem_usage = Math.max(max_mem_usage, mem_usage());
    }
  }

  public void end_of_iteration(
      String pptName,
      int num_samples,
      int num_static_vars,
      int num_orig_vars,
      int num_scalar_vars,
      int num_array_vars,
      int num_derived_scalar_vars,
      int num_derived_array_vars) {

    try (PrintWriter fout =
        new PrintWriter(Files.newBufferedWriter(Paths.get(filename), UTF_8, CREATE, APPEND))) {

      fout.print(pptName + ", " + max_mem_usage + ", " + num_samples + ", ");
      fout.print(num_static_vars + ", " + num_orig_vars + ", " + num_scalar_vars + ", ");
      fout.println(num_array_vars + ", " + num_derived_scalar_vars + ", " + num_derived_array_vars);

      max_mem_usage = mem_usage();
    } catch (java.io.IOException e) {
      System.out.println("could not open " + filename);
    }
  }

  public void stop() {
    keep_going = false;
  }
}
