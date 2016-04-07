//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Reflection;
using System.Text;
using EnvDTE;

namespace Microsoft.Research.Vcc.VSPackage {

  public class CompilerSettings {
    const string NoInherit = "$(NOINHERIT)";

    private string preprocessorDefinitions;
    private string additionalIncludeDirectories;
    private string forcedIncludeFiles;
    
    bool InheritPreprocessorDefinitions
    {
      get { return preprocessorDefinitions == null || !preprocessorDefinitions.Contains(NoInherit); }
    }
    
    bool InheritAdditionalIncludeDirectories
    {
      get { return additionalIncludeDirectories == null || !additionalIncludeDirectories.Contains(NoInherit); }
    }
    
    bool InheritForcedIncludeFiles
    {
      get { return forcedIncludeFiles == null || !forcedIncludeFiles.Contains(NoInherit); }
    }

    public CompilerSettings(ProjectItem prjItem) 
    {     
      dynamic vcProject = prjItem.ContainingProject.Object;
      dynamic file = prjItem.Object;
      var activeConf = prjItem.ContainingProject.ConfigurationManager.ActiveConfiguration;
      var activeSetting = activeConf.ConfigurationName + "|" + activeConf.PlatformName;

      CompilerSettings.AddSettingsFromVCFile(this, file, activeSetting);
      CompilerSettings.AddSettingsFromVCProject(this, vcProject, activeSetting);

      this.additionalIncludeDirectories = CompilerSettings.ExecuteMacroProject(vcProject, activeSetting, this.additionalIncludeDirectories);
      this.preprocessorDefinitions = CompilerSettings.ExecuteMacroProject(vcProject, activeSetting, this.preprocessorDefinitions);
      this.forcedIncludeFiles = CompilerSettings.ExecuteMacroProject(vcProject, activeSetting, this.forcedIncludeFiles);
    }

    public string ToVccOptions()
    {
        var args = new StringBuilder();

        args.Append(SplitAndFormatArgs(this.preprocessorDefinitions, "/p:/D", false));
        args.Append(SplitAndFormatArgs(this.additionalIncludeDirectories, "/p:/I", true));
        args.Append(SplitAndFormatArgs(this.forcedIncludeFiles, "/p:/I", true));

        return args.ToString();
    }

    private static void AddSettingsForCompilerTool(CompilerSettings settings, dynamic compilerTool)
    {
        string prePro = compilerTool.PreprocessorDefinitions;
        if (prePro != null && settings.InheritPreprocessorDefinitions)
            settings.preprocessorDefinitions += prePro + ";";

        string additionalDirs = compilerTool.AdditionalIncludeDirectories;
        if (additionalDirs != null && settings.InheritAdditionalIncludeDirectories)
            settings.additionalIncludeDirectories += additionalDirs + ";";

        string forcedIncludes = compilerTool.ForcedIncludeFiles;
        if (forcedIncludes != null && settings.InheritForcedIncludeFiles)
            settings.forcedIncludeFiles += forcedIncludes + ";";
    }

    private static void AddSettingsForCompilerToolNMake(CompilerSettings settings, dynamic nMakeTool)
    {
        var additionalOptions = GetSettingsFromAdditionalOptionsNMake(nMakeTool);

        string prePro = nMakeTool.PreprocessorDefinitions ?? "";
        if (settings.InheritPreprocessorDefinitions)
            settings.preprocessorDefinitions += prePro + ";" + additionalOptions.Item1 + ";";

        string additionalDirs = nMakeTool.IncludeSearchPath ?? "";
        if (settings.InheritAdditionalIncludeDirectories)
            settings.additionalIncludeDirectories += additionalDirs + ";" + additionalOptions.Item2 + ";";

        string forcedIncludes = nMakeTool.ForcedIncludes ?? "";
        if (settings.InheritForcedIncludeFiles)
            settings.forcedIncludeFiles += forcedIncludes + ";" + additionalOptions.Item3 + ";";
    }

    private static Tuple<string,string,string> GetSettingsFromAdditionalOptionsNMake(dynamic nMakeTool)
    {
        string additionalOptionsString = GetAdditionalOptionsValueNMake(nMakeTool);
        if (!String.IsNullOrEmpty(additionalOptionsString))
        {
            string[] additionalOptions = additionalOptionsString.Split(new[] {' '},
                                                                        StringSplitOptions.RemoveEmptyEntries);

            var defines = new StringBuilder();
            var includes = new StringBuilder();
            var forcedIncludes = new StringBuilder();

            foreach (var opt in additionalOptions)
            {
                if (opt.StartsWith("/D") || opt.StartsWith("-D"))
                {
                    defines.Append(opt.Substring(2)).Append(';');
                }

                if (opt.StartsWith("/I") || opt.StartsWith("-I"))
                {
                    includes.Append(opt.Substring(2)).Append(';');
                }

                if (opt.StartsWith("/FI") || opt.StartsWith("-FI"))
                {
                    forcedIncludes.Append(opt.Substring(3)).Append(';');
                }
            }

            return Tuple.Create(defines.ToString(), includes.ToString(), forcedIncludes.ToString());
        }

        else return Tuple.Create("", "", "");
    }

      private static string GetAdditionalOptionsValueNMake(dynamic nMakeTool)
      {
          const BindingFlags bindingFlags = BindingFlags.Instance | BindingFlags.FlattenHierarchy |
                                            BindingFlags.NonPublic | BindingFlags.Public;
          var strProp = nMakeTool.GetType().GetProperty("StronglyTypedRule", bindingFlags);
          var str = strProp.GetValue(nMakeTool, null);
          var aoProp = str.GetType().GetProperty("AdditionalOptions", bindingFlags);
          var ao = aoProp.GetValue(str, null);
          var vasProp = ao.GetType().GetProperty("ValueAsString", bindingFlags);
          return (string)vasProp.GetValue(ao, null);
      }

      /// <summary>
    /// Gets current Settings for an VCProject.
    /// Reads out Settings of the entry project.
    /// 1. Main Project Settings
    /// 2. Property Sheet Settings of current project.
    /// </summary>
    /// <param name="Project"></param>
    /// <param name="ActiveSetting">Active Setting Debug/Release ...</param>
    /// <param name="settings"></param>
    /// <returns>IncludeDirs and PreprocessorDefines</returns>
    private static void AddSettingsFromVCProject(CompilerSettings settings, dynamic Project, string ActiveSetting)
    {
      //Projects can have there settings in a PropertySheet or Tools Collection.     
      dynamic CollectionOfConfigurations = Project.Configurations;
       
      //Extract Config from Collection, with Name stored in ActiveSetting
      dynamic Configuration = CollectionOfConfigurations.Item(ActiveSetting);
      
      //1st collect Tool Data from Project Setting!  *****************************************************    
      dynamic Tools = Configuration.Tools;

      try {
        //Get VCCLCompilerTool
        dynamic CompilerTool = Tools.Item("VCCLCompilerTool");
        if (CompilerTool != null) AddSettingsForCompilerTool(settings, CompilerTool);
      } catch { }

      try {
          dynamic nMakeTool = Tools.Item("VCNMakeTool");
          if (nMakeTool != null) AddSettingsForCompilerToolNMake(settings, nMakeTool);
      } catch {  }

      //2nd collect Tool Data from PropertySheets! *****************************************************
      //PropertySheets Collection
      dynamic CollectionOfPropertySheets = Configuration.PropertySheets;
      //Count Sheets...
      int SheetCount = CollectionOfPropertySheets.Count;

      for (int i = 0; i < SheetCount; i++) {
        try {
          //Get Sheet from Collection
          dynamic PropertySheet = CollectionOfPropertySheets.Item(i + 1);
          //Get Tools                
          dynamic CollectionOfTools = PropertySheet.Tools;
          //Get VCCLCompilerTool
          dynamic CompilerTool = CollectionOfTools.Item("VCCLCompilerTool");
          if (CompilerTool != null) AddSettingsForCompilerTool(settings, CompilerTool);

          dynamic nMakeTool = CollectionOfTools.Item("VCNMakeTool");
          if (nMakeTool != null) AddSettingsForCompilerToolNMake(settings, nMakeTool);
        } catch { }
      }
    }

    /// <summary>
    /// Gets current Settings for an VCFile.
    /// </summary>
    /// <returns>IncludeDirs and PreprocessorDefines</returns>
    private static void AddSettingsFromVCFile(CompilerSettings settings, dynamic File, string ActiveSetting)
    {
      //Extract Config from Collection, with Name stored in ActiveSetting
      dynamic CollectionOfFileConfigurations = File.FileConfigurations;
      dynamic FileConfiguration = CollectionOfFileConfigurations.Item(ActiveSetting);
      
      try {
        //Get Tool  
        dynamic CompilerTool = FileConfiguration.Tool;
        if (CompilerTool != null) AddSettingsForCompilerTool(settings, CompilerTool);
      } catch { }
    }

    private static string ExecuteMacroProject(dynamic Project, string ActiveConfiguration, string MacroToEvaluate)
    {
      dynamic CollectionOfConfigurations = Project.Configurations;
      //Extract Config from Collection, with Name stored in ActiveSetting
      dynamic Configuration = CollectionOfConfigurations.Item(ActiveConfiguration);
      return Configuration.Evaluate(MacroToEvaluate);
    }

      private static string SplitAndFormatArgs(string options, string optionPrefix, bool quoteFileNames)
    {
        if (String.IsNullOrEmpty(options)) return "";

        StringBuilder result = new StringBuilder();
        var opts = options.Split(new[] {';'}, StringSplitOptions.RemoveEmptyEntries);
        foreach (var opt in opts)
        {
            if (opt == NoInherit) continue;
            if (quoteFileNames && opt.Contains(" ") && !opt.StartsWith("\""))
                result.Append(optionPrefix).Append('"').Append(opt).Append('"').Append(' ');
            else
                result.Append(optionPrefix).Append(opt).Append(' ');
        }

        return result.ToString();
    }
  }
}
