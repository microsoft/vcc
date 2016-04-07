using Microsoft.VisualStudio.TestTools.UnitTesting;

namespace Coverage
{
  /// <summary>
  /// Summary description for UnitTest1
  /// </summary>
  [TestClass]
  public class UnitTest1
  {
    /// <summary>
    ///Gets or sets the test context which provides
    ///information about and functionality for the current test run.
    ///</summary>
    public TestContext TestContext { get; set; }

    #region Additional test attributes
    //
    // You can use the following additional attributes as you write your tests:
    //
    // Use ClassInitialize to run code before running the first test in the class
    // [ClassInitialize()]
    // public static void MyClassInitialize(TestContext testContext) { }
    //
    // Use ClassCleanup to run code after all tests in a class have run
    // [ClassCleanup()]
    // public static void MyClassCleanup() { }
    //
    // Use TestInitialize to run code before running each test 
    // [TestInitialize()]
    // public void MyTestInitialize() { }
    //
    // Use TestCleanup to run code after each test has run
    // [TestCleanup()]
    // public void MyTestCleanup() { }
    //
    #endregion

    [TestMethod]
    [DeploymentItem("src\\vcc\\boogie\\z3.exe")]
    [DeploymentItem("src\\vcc\\boogie\\TypedUnivBackPred2.sx")]
    public void RunSuite() {
      Assert.IsTrue(System.IO.File.Exists("z3.exe"));
      Assert.IsTrue(Microsoft.Research.Vcc.VccCommandLineHost.Main(new[] { "/s", "done", "vcc2", "examples" }) == 0);
    }
  }
}
