using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Net;
using System.Text;
using System.Text.RegularExpressions;
using Newtonsoft.Json.Linq;
using eWayCRM.API.Exceptions;
using System.Net.Sockets;
using System.Net.NetworkInformation;
using System.Security.Cryptography;
using eWay.Core.Net;
using System.Linq.Expressions;
using System.Xml;
using eWayCRM.API.EventArgs;

namespace eWayCRM.API
{
    /// <summary>
    /// eWay-CRM API Connector class.
    /// This class helps to manage the connection to the eWay-CRM API.
    /// </summary>
    public class Connection
    {
        private readonly string baseServiceUri;
        private string serviceUri;
        private bool oldServiceUriUsed;
        private readonly string username;
        private readonly string passwordHash;
        private readonly string appIdentifier;
        private readonly string clientMachineIdentifier;
        private string accessToken;
        private readonly bool useDefaultCredentials;
        private readonly NetworkCredential networkCredential;
        private const string _uploadMethodName = "SaveBinaryAttachment";
        private const string _loginMethodName = "LogIn";
        private static readonly MD5 _md5Hash = MD5.Create();

        /// <summary>
        /// Event used to refresh access token.
        /// </summary>
        public event System.EventHandler<AccessTokenEventArgs> RefreshAccessToken;

        private Guid? sessionId;

        /// <summary>
        /// Gets the user Guid.
        /// </summary>
        public Guid UserGuid
        {
            get;
            private set;
        }

        /// <summary>
        /// Gets the API version.
        /// </summary>
        public Version Version
        {
            get;
            private set;
        }

        /// <summary>
        /// Gets the base WebService URL.
        /// </summary>
        public string WebServiceUrl => this.baseServiceUri;

        /// <summary>
        /// Initializes a new instance of the <see cref="Connection" /> class.
        /// </summary>
        /// <param name="apiServiceUri">The API service URI. Ex. 'https://server.mycompany.com/eway' or 'https://server.local:4443/eWay/WcfService/Service.svc'</param>
        /// <param name="username">The eWay-CRM username. Ex. 'jsmith'.</param>
        /// <param name="passwordHash">Password hash. Use the hash made with HashPassword.exe. MD5 hashes are accepted as well (unless AD HTTP Authentication between WS and WCF is activated).</param>
        /// <param name="appIdentifier">The application identifier. Must contain at least two alphabetic characters on the beginning and at least one numeric character at the end.</param>
        /// <param name="clientMachineIdentifier">The unique identifier, of the client machine. Usually a MAC address is used. Optional. If you leave it null, MAC address is used.</param>
        /// <param name="useDefaultCredentials">True to authenticate HTTP request using the default credentials of the currently logged on user.</param>
        /// <param name="networkCredential">Network credential used to authenticate HTTP request.</param>
        /// <param name="accessToken">Access token from OAuth.</param>
        /// <exception cref="ArgumentNullException">eWay-CRM API service uri was not supplied. - apiServiceUri
        /// or
        /// eWay-CRM username was not supplied. - username
        /// or
        /// eWay-CRM password hash was not supplied. - passwordHash
        /// or
        /// The client app identifier was not supplied. - appIdentifier</exception>
        /// <exception cref="ArgumentException">The *.asmx file is not the right service endpoint. This connection is meant to be used against the eWay-CRM WCF API. - apiServiceUri</exception>
        public Connection(string apiServiceUri, string username, string passwordHash, string appIdentifier = "eWayCRM.API.CSharpConnector10", string clientMachineIdentifier = null,
            bool useDefaultCredentials = false, NetworkCredential networkCredential = null, string accessToken = null)
        {
            if (string.IsNullOrEmpty(apiServiceUri))
                throw new ArgumentNullException(nameof(apiServiceUri), "eWay-CRM API service uri was not supplied.");

            if (string.IsNullOrEmpty(username))
                throw new ArgumentNullException(nameof(username), "eWay-CRM username was not supplied.");

            if (string.IsNullOrEmpty(passwordHash) && !useDefaultCredentials && networkCredential == null && string.IsNullOrEmpty(accessToken))
                throw new ArgumentNullException(nameof(passwordHash), "eWay-CRM password hash was not supplied.");

            if (string.IsNullOrEmpty(appIdentifier))
                throw new ArgumentNullException(nameof(appIdentifier), "The client app identifier was not supplied.");

            if (apiServiceUri.EndsWith(".asmx", StringComparison.OrdinalIgnoreCase))
                throw new ArgumentException("The *.asmx file is not the right service endpoint. This connection is meant to be used against the eWay-CRM WCF API.", nameof(apiServiceUri));

            if (!Regex.IsMatch(appIdentifier, "^[a-zA-Z][a-zA-Z].*\\d$"))
                throw new ArgumentException("The client app identifier must contain at least two alphabetic characters on the beginning and at least one numeric character at the end.", nameof(appIdentifier));

            if (useDefaultCredentials && !apiServiceUri.StartsWith("https://"))
                throw new ArgumentException("Secure communication (https) has to be used with useDefaultCredentials parameter", nameof(useDefaultCredentials));

            if (networkCredential != null && !apiServiceUri.StartsWith("https://"))
                throw new ArgumentException("Secure communication (https) has to be used with networkCredential parameter", nameof(networkCredential));

            if (networkCredential != null && useDefaultCredentials)
                throw new ArgumentException("Parameter networkCredential should not be used together with useDefaultCredentials", nameof(networkCredential));

            if (string.IsNullOrEmpty(clientMachineIdentifier))
            {
                clientMachineIdentifier = GetClientIdentification(apiServiceUri);
                if (string.IsNullOrEmpty(clientMachineIdentifier))
                    throw new ClientMachineIdentifierDeterminationException($"Unable to determine the client machine unique identifier automatically. Please supply it manually via the '{nameof(clientMachineIdentifier)}' argument.");
            }

            if (apiServiceUri.EndsWith(".svc", StringComparison.OrdinalIgnoreCase))
            {
                this.serviceUri = apiServiceUri;
                this.baseServiceUri = apiServiceUri.Replace("/WcfService/Service.svc", "/").Replace("/InsecureAPI.svc", "/").Replace("/API.svc", "/");
            }
            else
            {
                this.serviceUri = this.GetApiServiceUrl(apiServiceUri);
                this.baseServiceUri = apiServiceUri;
            }

            this.username = username;
            this.passwordHash = passwordHash;
            this.appIdentifier = appIdentifier;
            this.clientMachineIdentifier = clientMachineIdentifier;
            this.useDefaultCredentials = useDefaultCredentials;
            this.networkCredential = networkCredential;
            this.accessToken = accessToken;
        }

        private string GetApiServiceUrl(string baseUri, bool useOldUrl = false)
        {
            string path = useOldUrl ? "WcfService/Service.svc" : (baseUri.StartsWith("http://") ? "InsecureAPI.svc" : "API.svc");
            UriBuilder builder = new UriBuilder(baseUri);
            if (builder.Path.EndsWith("/"))
            {
                builder.Path = builder.Path + path;
            }
            else
            {
                builder.Path = builder.Path + "/" + path;
            }

            return builder.ToString();
        }

        /// <summary>
        /// Calls the given method against the eWay-CRM API.
        /// </summary>
        /// <param name="methodName">Name of the method. Ex. 'GetCompanies'</param>
        /// <returns>
        /// JSON data returned by the API service.
        /// </returns>
        /// <exception cref="ArgumentNullException">
        /// The method name was not supplied. - methodName
        /// or
        /// data - The parameter JSON data were not supplied. Supply at least an empty JSON object.
        /// </exception>
        /// <exception cref="LoginException">
        /// Logging into eWay-CRM was unsuccessful.
        /// </exception>
        /// <exception cref="ResponseException">
        /// Method calling ended up badly.
        /// </exception>
        public JObject CallMethod(string methodName)
        {
            if (string.IsNullOrEmpty(methodName))
                throw new ArgumentNullException(nameof(methodName), "The method name was not supplied.");

            return this.CallMethod(methodName, JObject.FromObject(new { }));
        }

        /// <summary>
        /// Calls the given method against the eWay-CRM API.
        /// </summary>
        /// <param name="methodName">Name of the method. Ex. 'GetCompanies'</param>
        /// <param name="jsonData">The JSON parameters posted to the method. Posting sessionId is not necessary. Ex.:
        /// {
        ///     transmitObject: {
        ///         FileAs: "My New Company"
        ///     }
        /// }</param>
        /// <returns>
        /// JSON data returned by the API service.
        /// </returns>
        /// <exception cref="ArgumentNullException">
        /// The method name was not supplied. - methodName
        /// or
        /// data - The parameter JSON data were not supplied. Supply at least an empty JSON object.
        /// </exception>
        /// <exception cref="LoginException">
        /// Logging into eWay-CRM was unsuccessful.
        /// </exception>
        /// <exception cref="ResponseException">
        /// Method calling ended up badly.
        /// </exception>
        public JObject CallMethod(string methodName, string jsonData)
        {
            if (string.IsNullOrEmpty(methodName))
                throw new ArgumentNullException(nameof(methodName), "The method name was not supplied.");

            if (string.IsNullOrEmpty(jsonData))
                throw new ArgumentNullException(nameof(jsonData), "JSON data were not supplied.");

            return this.CallMethod(methodName, JObject.Parse(jsonData));
        }

        /// <summary>
        /// Calls the given method against the eWay-CRM API.
        /// </summary>
        /// <param name="methodName">Name of the method. Ex. 'SaveCompany'</param>
        /// <param name="data">The JSON parameters posted to the method. Posting sessionId is not necessary. Ex.:
        /// {
        ///     transmitObject: {
        ///         FileAs: "My New Company"
        ///     }
        /// }</param>
        /// <returns>
        /// JSON data returned by the API service.
        /// </returns>
        /// <exception cref="ArgumentNullException">
        /// The method name was not supplied. - methodName
        /// or
        /// data - The parameter JSON data were not supplied. Supply at least an empty JSON object.
        /// </exception>
        /// <exception cref="LoginException">
        /// Logging into eWay-CRM was unsuccessful.
        /// </exception>
        /// <exception cref="ResponseException">
        /// Method calling ended up badly.
        /// </exception>
        public JObject CallMethod(string methodName, JObject data)
        {
            if (string.IsNullOrEmpty(methodName))
                throw new ArgumentNullException(nameof(methodName), "The method name was not supplied.");

            if (data == null)
                throw new ArgumentNullException(nameof(data), "The parameter JSON data were not supplied. Supply at least an empty JSON object.");

            return this.CallMethod(methodName, data, true);
        }

        private bool TryRefreshAccessToken()
        {
            if (this.RefreshAccessToken == null)
                return false;

            var eventArgs = new AccessTokenEventArgs();
            this.RefreshAccessToken(this, eventArgs);

            if (string.IsNullOrEmpty(eventArgs.AccessToken))
                return false;

            this.accessToken = eventArgs.AccessToken;
            return true;
        }

        private JObject CallMethod(string methodName, JObject data, bool repeatSession)
        {
            JObject d = new JObject(data);
            this.EnsureLogin();
            d.Add("sessionId", this.sessionId);
            JObject response = this.Call(methodName, d);
            string returnCode = response.GetValue("ReturnCode").ToString();

            if (returnCode == "rcBadSession" && repeatSession)
            {
                try
                {
                    this.LogIn();
                }
                catch (LoginException ex)
                {
                    if (ex.ReturnCode != "rcBadAccessToken")
                        throw;

                    if (!this.TryRefreshAccessToken())
                        throw;
                    
                    this.LogIn();
                }

                return this.CallMethod(methodName, data, false);
            }

            if (response.GetValue("ReturnCode").ToString() != "rcSuccess")
                throw new ResponseException(methodName, response.GetValue("ReturnCode").ToString(), response.GetValue("Description").ToString());

            return response;
        }

        /// <summary>
        /// Forces LogIn method to be called if it was not called before.
        /// </summary>
        public void EnsureLogin()
        {
            if (this.sessionId == null)
            {
                this.LogIn();
            }
        }

        /// <summary>
        /// If there is session it tries to destroy it.
        /// </summary>
        /// <returns>Response from API or null when there is no active session.</returns>
        public JObject LogOut()
        {
            if (!this.sessionId.HasValue)
                return null;

            return this.Call("LogOut", JObject.FromObject(new
            {
                sessionId = this.sessionId
            }));
        }

        private void LogIn()
        {
            JObject response = this.Call(_loginMethodName, JObject.FromObject(new
            {
                userName = this.username,
                passwordHash = this.passwordHash,
                appVersion = this.appIdentifier,
                clientMachineIdentifier = this.clientMachineIdentifier
            }));

            string returnCode = response.GetValue("ReturnCode").ToString();
            if (returnCode == "rcOAuthRequired")
                throw new OAuthRequiredException(returnCode, response.GetValue("Description").ToString());
            
            if (returnCode != "rcSuccess")
                throw new LoginException(returnCode, response.GetValue("Description").ToString());

            this.sessionId = new Guid(response.Value<string>("SessionId"));
            this.UserGuid = new Guid(response.Value<string>("UserItemGuid"));
            this.Version = new Version(response.Value<string>("WcfVersion"));
        }

        private JObject Call(string methodName, JObject data)
        {
            string responseJson = null;

            this.Call(methodName, data, (stream) =>
            {
                using (StreamReader streamReader = new StreamReader(stream))
                {
                    responseJson = streamReader.ReadToEnd();
                }
            });

            if (string.IsNullOrEmpty(responseJson))
                throw new InvalidOperationException("Wcf returned nothing. That's strange.");

            JObject result = JObject.Parse(responseJson);

            return result;
        }

        private void Call(string methodName, JObject data, Action<Stream> readStreamAction)
        {
            if (string.IsNullOrEmpty(methodName))
                throw new ArgumentNullException(nameof(methodName));

            if (data == null)
                throw new ArgumentNullException(nameof(data));

            HttpWebRequest webRequest = (HttpWebRequest)WebRequest.Create(this.GetMethodUri(methodName));
            webRequest.Method = WebRequestMethods.Http.Post;
            webRequest.UseDefaultCredentials = this.useDefaultCredentials;
            webRequest.ContentType = "application/json";

            if (methodName == _loginMethodName && !string.IsNullOrEmpty(this.accessToken))
            {
                webRequest.Headers.Add(HttpRequestHeader.Authorization, $"Bearer {this.accessToken}");
            }

            if (!useDefaultCredentials)
            {
                webRequest.Credentials = this.networkCredential;
            }

            byte[] postBytes = Encoding.UTF8.GetBytes(data.ToString());
            webRequest.ContentLength = postBytes.Length;
            using (Stream dataStream = webRequest.GetRequestStream())
            {
                dataStream.Write(postBytes, 0, postBytes.Length);
            }

            try
            {
                using (HttpWebResponse httpResponse = (HttpWebResponse)webRequest.GetResponse())
                {
                    using (Stream responseStream = httpResponse.GetResponseStream())
                    {
                        if (responseStream != null)
                        {
                            readStreamAction(responseStream);
                        }
                    }
                }
            }
            catch (WebException ex)
            {
                if (!(ex.Response is HttpWebResponse))
                    throw;

                var statusCode = ((HttpWebResponse)ex.Response).StatusCode;

                if (!this.oldServiceUriUsed && statusCode == HttpStatusCode.NotFound && methodName == _loginMethodName && this.passwordHash != null)
                {
                    this.serviceUri = this.GetApiServiceUrl(this.baseServiceUri, true);
                    this.oldServiceUriUsed = true;

                    this.Call(methodName, data, readStreamAction);
                    return;
                }

                if (statusCode == HttpStatusCode.Unauthorized && !string.IsNullOrEmpty(this.accessToken) && this.TryRefreshAccessToken())
                {
                    this.Call(methodName, data, readStreamAction);
                    return;
                }

                throw;
            }
        }

        /// <summary>
        /// Calls method for uploading binary attachments against the eWay-CRM API.
        /// </summary>
        /// <param name="filePath">Path to the attachment to be uploaded (including the file). Is unnecessary if the method is supplied with stream and fileName. Ex. 'C:\Users\User\Documents\File.txt'</param>
        /// <param name="itemGuid">The item unique identifier.  Will be generated for you.</param>
        /// <param name="fileName">Name of the file to be uploaded. Is unnecessary if the method is supplied with filePath. Ex. 'File.txt'</param>
        /// <returns>
        /// JSON data returned by the API service.
        /// </returns>
        /// <exception cref="LoginException">
        /// Logging into eWay-CRM was unsuccessful.
        /// </exception>
        /// <exception cref="ResponseException">
        /// Method calling ended up badly.
        /// </exception>
        public JObject UploadFile(string filePath, out Guid itemGuid, string fileName = null)
        {
            itemGuid = Guid.NewGuid();
            return this.UploadFile(filePath, itemGuid, fileName);
        }

        /// <summary>
        /// Calls method for uploading binary attachments against the eWay-CRM API.
        /// </summary>
        /// <param name="filePath">Path to the attachment to be uploaded (including the file). Is unnecessary if the method is supplied with stream and fileName. Ex. 'C:\Users\User\Documents\File.txt'</param>
        /// <param name="itemGuid">Unique identifier  of attachment to be uploaded. Ex. 'XXXXXXXX-XXXX-XXXX-XXXX-XXXXXXXXXXXX'</param>
        /// <param name="fileName">Name of the file to be uploaded. Is unnecessary if the method is supplied with filePath. Ex. 'File.txt'</param>
        /// <returns>
        /// JSON data returned by the API service.
        /// </returns>
        /// <exception cref="LoginException">
        /// Logging into eWay-CRM was unsuccessful.
        /// </exception>
        /// <exception cref="ResponseException">
        /// Method calling ended up badly.
        /// </exception>
        public JObject UploadFile(string filePath, Guid itemGuid, string fileName = null)
        {
            if (string.IsNullOrEmpty(filePath))
                throw new ArgumentNullException(nameof(filePath));

            if (!File.Exists(filePath))
                throw new FileNotFoundException("The file for uploading was not found.", filePath);

            if (string.IsNullOrEmpty(fileName))
                fileName = Path.GetFileName(filePath);

            using (FileStream fileStream = new FileStream(filePath, FileMode.Open, FileAccess.Read))
            {
                return this.UploadFile(fileStream, itemGuid, fileName);
            }
        }

        /// <summary>
        /// Calls method for uploading binary attachments against the eWay-CRM API.
        /// </summary>
        /// <param name="stream">Stream used for uploading the attachment. File stream will be used if not supplied.. Ex.:'FileStream fileStream = new FileStream(filePath, FileMode.Open, FileAccess.Read)'</param>
        /// <param name="itemGuid">The item unique identifier.  Will be generated for you.</param>
        /// <param name="fileName">Name of the file to be uploaded. Ex. 'File.txt'</param>
        /// <returns>
        /// JSON data returned by the API service.
        /// </returns>
        /// <exception cref="ArgumentException">
        /// Stream must be able to read! - stream
        /// </exception>
        /// <exception cref="LoginException">
        /// Logging into eWay-CRM was unsuccessful.
        /// </exception>
        /// <exception cref="ResponseException">
        /// Method calling ended up badly.
        /// </exception>
        public JObject UploadFile(Stream stream, out Guid itemGuid, string fileName)
        {
            itemGuid = Guid.NewGuid();
            return this.UploadFile(stream, itemGuid, fileName);
        }

        /// <summary>
        /// Calls method for uploading binary attachments against the eWay-CRM API.
        /// </summary>
        /// <param name="stream">Stream used for uploading the attachment. File stream will be used if not supplied.. Ex.:'FileStream fileStream = new FileStream(filePath, FileMode.Open, FileAccess.Read)'</param>
        /// <param name="itemGuid">Unique identifier  of attachment to be uploaded. Ex. 'XXXXXXXX-XXXX-XXXX-XXXX-XXXXXXXXXXXX'</param>
        /// <param name="fileName">Name of the file to be uploaded. Ex. 'File.txt'</param>
        /// <returns>
        /// JSON data returned by the API service.
        /// </returns>
        /// <exception cref="ArgumentException">
        /// Stream must be able to read! - stream
        /// </exception>
        /// <exception cref="LoginException">
        /// Logging into eWay-CRM was unsuccessful.
        /// </exception>
        /// <exception cref="ResponseException">
        /// Method calling ended up badly.
        /// </exception>
        public JObject UploadFile(Stream stream, Guid itemGuid, string fileName)
        {
            if (stream == null)
                throw new ArgumentNullException(nameof(stream));

            if (string.IsNullOrEmpty(fileName))
                throw new ArgumentNullException(nameof(fileName));

            return this.UploadFile(itemGuid, stream, fileName, true);
        }

        /// <summary>
        /// Uploads document to eWay-CRM API. It calls UploadFile to upload binary data and SaveDocument to create the document entity.
        /// </summary>
        /// <param name="filePath">Path to file.</param>
        /// <param name="itemGuid">New document GUID.</param>
        /// <returns></returns>
        public JObject UploadDocument(string filePath, Guid itemGuid)
        {
            if (string.IsNullOrEmpty(filePath))
                throw new ArgumentNullException(nameof(filePath));

            if (!File.Exists(filePath))
                throw new FileNotFoundException("The file for uploading was not found.", filePath);

            // Upload BinaryData
            var response = this.UploadFile(filePath, itemGuid);
            if (response.GetValue("ReturnCode").ToString() != "rcSuccess")
                throw new ResponseException("UploadFile", response.GetValue("ReturnCode").ToString(), response.GetValue("Description").ToString());

            // Create Document
            response = this.CallMethod("SaveDocument", JObject.FromObject(new
            {
                transmitObject = new
                {
                    ItemGUID = itemGuid,
                    FileAs = Path.GetFileName(filePath),
                    DocName = Path.GetFileNameWithoutExtension(filePath),
                    Extension = Path.GetExtension(filePath).Trim('.'),
                    DocSize = new FileInfo(filePath).Length
                }
            }));
            
            if (response.GetValue("ReturnCode").ToString() != "rcSuccess")
                throw new ResponseException("SaveDocument", response.GetValue("ReturnCode").ToString(), response.GetValue("Description").ToString());

            return response;
        }

        /// <summary>
        /// Downloads file from API to output stream.
        /// </summary>
        /// <param name="itemGuid">Guid of the document or email.</param>
        /// <param name="revision">Revision of the document or email.</param>
        /// <param name="outputStream">The output stream.</param>
        public void DownloadFile(Guid itemGuid, int revision, Stream outputStream)
        {
            JObject data = new JObject();
            data.Add("sessionId", this.sessionId);
            data.Add("itemGuid", itemGuid.ToString());
            data.Add("revision", revision);

            this.Call("GetBinaryAttachment", data, (stream) =>
            {
                stream.CopyTo(outputStream);
            });
        }

        /// <summary>
        /// Gets information about latest document revision.
        /// </summary>
        /// <param name="itemGuid">Document Guid.</param>
        /// <returns></returns>
        public JObject GetLatestRevision(Guid itemGuid)
        {
            JObject data = new JObject();
            data.Add("sessionId", this.sessionId);
            data.Add("documtentGuid", itemGuid.ToString());

            return this.Call("GetLatestRevision", data);
        }

        /// <summary>
        /// Use this method to hash the eWay-CRM password in case you don't have it already available encrypted or hashed.
        /// </summary>
        /// <param name="input">Password to be hashed.</param>
        /// <returns>Hash for usage in <see cref="Connection"/> constructor.</returns>
        public static string HashPassword(string input)
        {
            byte[] data = _md5Hash.ComputeHash(Encoding.UTF8.GetBytes(input));
            StringBuilder sBuilder = new StringBuilder();
            for (int i = 0; i < data.Length; i++)
            {
                sBuilder.Append(data[i].ToString("x2"));
            }
            return sBuilder.ToString();
        }

        /// <summary>
        /// Gets web service version based on URL.
        /// </summary>
        /// <param name="webServiceUrl">Web service URL.</param>
        /// <param name="version">Version.</param>
        /// <returns></returns>
        public static bool TryGetWebServiceVersion(string webServiceUrl, out Version version)
        {
            if (string.IsNullOrEmpty(webServiceUrl))
                throw new ArgumentNullException(nameof(webServiceUrl));

            version = new Version();

            HttpWebRequest request = (HttpWebRequest)WebRequest.Create(new Uri(UrlBuilder.Combine(webServiceUrl, "eWayWS.asmx/GetInfo")));
            request.Method = "GET";
            request.ContentType = "application/xml";
            request.Accept = "application/xml";

            string xmlResponse;
            using (HttpWebResponse httpResponse = (HttpWebResponse)request.GetResponse())
            {
                using (Stream responseStream = httpResponse.GetResponseStream())
                {
                    if (responseStream == null)
                        return false;

                    using (StreamReader streamReader = new StreamReader(responseStream))
                    {
                        xmlResponse = streamReader.ReadToEnd();
                    }
                }
            }

            if (string.IsNullOrEmpty(xmlResponse))
                return false;

            var xmlDocument = new XmlDocument();
            xmlDocument.LoadXml(xmlResponse);

            var nsManager = new XmlNamespaceManager(xmlDocument.NameTable);
            nsManager.AddNamespace("ns", "http://tempuri.org/");

            var webServiceVersion = xmlDocument.SelectSingleNode("//ns:InfoResponse/ns:WebServiceVersion", nsManager);
            if (webServiceVersion == null)
                return false;

            version = new Version(webServiceVersion.InnerText);
            return true;
        }

        /// <summary>
        /// Calls Get[FolderName]ByItemGuids with chunking.
        /// </summary>
        /// <param name="methodName">Name of the method.</param>
        /// <param name="itemGuids">Identifiers of items.</param>
        /// <param name="includeForeignKeys">If set to True, the JSON result will contain foreign keys/items fields made from the 1:N relations as well.</param>
        /// <param name="includeRelations">If set to True, the JSON result will contain the relations as well.</param>
        /// <returns></returns>
        public JArray GetItemsByItemGuids(string methodName, IEnumerable<Guid> itemGuids, bool includeForeignKeys = false, bool includeRelations = false)
        {
            List<JToken> items = new List<JToken>(itemGuids.Count());

            foreach (IEnumerable<Guid> itemsGroup in itemGuids.Select((item, index) => new { item, index }).GroupBy(x => x.index / 192, x => x.item))
            {
                items.AddRange(this.CallMethod(methodName, JObject.FromObject(new
                {
                    itemGuids = new JArray(itemsGroup),
                    includeForeignKeys,
                    includeRelations
                }))["Data"]);
            }

            return new JArray(items);
        }

        private JObject UploadFile(Guid itemGuid, Stream stream, string fileName, bool repeatSession)
        {
            this.EnsureLogin();
            JObject response = this.Upload(itemGuid, stream, fileName);
            if (response.GetValue("ReturnCode").ToString() == "rcBadSession" && repeatSession)
            {
                this.LogIn();
                return this.UploadFile(itemGuid, stream, fileName, false);
            }
            if (response.GetValue("ReturnCode").ToString() != "rcSuccess")
                throw new ResponseException(_uploadMethodName, response.GetValue("ReturnCode").ToString(), response.GetValue("Description").ToString());
            return response;
        }

        private JObject Upload(Guid itemGuid, Stream stream, string fileName)
        {
            if (!stream.CanRead)
                throw new ArgumentException("Stream must be able to read!", nameof(stream));

            HttpWebRequest webRequest = (HttpWebRequest)WebRequest.Create(this.GetFileUploadUri(itemGuid, fileName));
            webRequest.Method = WebRequestMethods.Http.Post;
            webRequest.ContentType = "application/octet-stream";

            using (Stream writeStream = webRequest.GetRequestStream())
            {
                byte[] buffer = new byte[4 * 1024];
                int bytesRead = 0;
                while ((bytesRead = stream.Read(buffer, 0, buffer.Length)) != 0)
                {
                    writeStream.Write(buffer, 0, bytesRead);
                }
            }

            string responseJson = null;
            using (HttpWebResponse httpResponse = (HttpWebResponse)webRequest.GetResponse())
            {
                using (Stream responseStream = httpResponse.GetResponseStream())
                {
                    if (responseStream != null)
                    {
                        using (StreamReader streamReader = new StreamReader(responseStream))
                        {
                            responseJson = streamReader.ReadToEnd();
                        }
                    }
                }
            }
            if (string.IsNullOrEmpty(responseJson))
                throw new InvalidOperationException("Wcf returned nothing. That's strange.");

            JObject result = JObject.Parse(responseJson);

            return result;
        }

        private string GetMethodUri(string methodName)
        {
            return this.serviceUri + "/" + methodName;
        }

        private string GetFileUploadUri(Guid itemGuid, string FileName)
        {
            return ($"{this.serviceUri}/{_uploadMethodName}?sessionId={this.sessionId}&itemGuid={itemGuid}&fileName={FileName}");
        }

        private static string GetClientIdentification(string uriString)
        {
            if (string.IsNullOrEmpty(uriString))
                throw new ArgumentNullException(nameof(uriString));

            var request = (HttpWebRequest)WebRequest.Create(uriString);
            var localAddress = GetLocalAddress(request.ServicePoint.Address.DnsSafeHost, request.ServicePoint.Address.Port);
            if (localAddress == null)
                return Environment.MachineName;

            var networkInterface = NetworkInterface.GetAllNetworkInterfaces()
                .Where(n => n.GetIPProperties().UnicastAddresses.Any(x => x.Address.Equals(localAddress)))
                .FirstOrDefault();

            if (networkInterface == null)
                return localAddress.ToString();

            string physicalAddress = string.Join(":", networkInterface.GetPhysicalAddress().GetAddressBytes().Select(b => b.ToString("X2")));
            if (string.IsNullOrEmpty(physicalAddress))
                return localAddress.ToString();

            return physicalAddress;
        }

        private static IPAddress GetLocalAddress(string hostName, int port)
        {
            try
            {
                TcpClient tcpClient = new TcpClient(hostName, port);
                return ((IPEndPoint)tcpClient.Client.LocalEndPoint).Address;
            }
            catch (SocketException)
            {
                return null;
            }
        }
    }
}
